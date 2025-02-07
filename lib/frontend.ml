open Core
open Result.Let_syntax
module Log = (val Logs.src_log Logging.frontend_src : Logs.LOG)

type error =
  [ `ConversionError of string
  | `HeaderTypeNotDeclaredError of string
  | `NotImplementedError of string
  ]

module ParserCfg = struct
  module type Comp = sig
    type t

    val sexp_of_t : t -> Sexp.t
    val t_of_sexp : Sexp.t -> t
    val compare : t -> t -> int
  end

  module rec CfgNode : sig
    type t =
      { name : string;
        statements : Syntax.Command.t list;
        successors : EdgeSet.t
      }
    [@@deriving compare, sexp]

    include Comp with type t := t
  end = struct
    module T = struct
      type t =
        { name : string;
          statements : Syntax.Command.t list;
          successors : EdgeSet.t
        }
      [@@deriving compare, sexp]
    end

    include T
    include Comparable.Make (T)
  end

  and EdgeType : sig
    type t =
      | Default
      | Match of Syntax.Instance.t * string * Bigint.t
    [@@deriving compare, sexp]

    include Comp with type t := t
  end = struct
    module T = struct
      type t =
        | Default
        | Match of Syntax.Instance.t * string * Bigint.t
      [@@deriving compare, sexp]
    end

    include T
    include Comparable.Make (T)
  end

  and Edge : sig
    type t =
      { node : CfgNode.t;
        typ : EdgeType.t
      }
    [@@deriving compare, sexp]

    include Comp with type t := t
  end = struct
    module T = struct
      type t =
        { node : CfgNode.t;
          typ : EdgeType.t
        }
      [@@deriving compare, sexp]
    end

    include T
    include Comparable.Make (T)
  end

  and EdgeSet : sig
    include Set.S with type Elt.t := Edge.t
  end =
    Set.Make (Edge)

  let mk_empty_node name =
    CfgNode.{ name; statements = []; successors = EdgeSet.empty }
end

let bigint_to_int bint =
  Bigint.to_int bint
  |> Result.of_option ~error:(`ConversionError "Can't convert Bigint to int.")

let bigint_to_bv (n : Bigint.t) (size : int) =
  let%bind int_value = bigint_to_int n in
  let bv_str = Utils.bin_of_int int_value in
  let size_diff = size - String.length bv_str in
  if size_diff < 0 then
    Error
      (`ConversionError
        (Printf.sprintf "Can't fit value '%s' into a bitvector of size %d."
           (Bigint.to_string n) size))
  else return (Syntax.bv_s (String.init size_diff ~f:(fun _ -> '0') ^ bv_str))

let field_size_from_type (hdr_type : Petr4.Types.Type.t) =
  match snd hdr_type with
  | BitType expr -> (
    match snd expr with
    | Petr4.Types.Expression.Int (_, n) -> return n.value
    | _ ->
      Error
        (`NotImplementedError
          "Not implemented (Frontend.field_size_from_type - Not an Int)"))
  | _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.field_size_from_type - not a BitType)")

let add_header_type_decl
    (header_type_decls : Syntax.Declaration.field list String.Map.t)
    ((_, name) : Petr4.Types.P4String.t)
    (fields : Petr4.Types.Declaration.field list) =
  let%map fields =
    List.map fields ~f:(fun (_, field) ->
        let%bind field_size = field_size_from_type field.typ in
        let%map n = bigint_to_int field_size in
        Syntax.Declaration.{ name = snd field.name; typ = n })
    |> Utils.sequence_error
  in
  Map.set header_type_decls ~key:name ~data:fields

let build_header_table (Petr4.Types.Program decls) =
  let%bind header_type_decls =
    List.fold decls ~init:(Ok String.Map.empty)
      ~f:(fun header_type_decls decl ->
        Result.bind header_type_decls ~f:(fun acc ->
            match snd decl with
            | Header { name; fields; _ } -> add_header_type_decl acc name fields
            | Struct { name; fields; _ } ->
              let type_name = snd name in
              if String.(type_name = "headers" || type_name = "metadata") then
                return acc
              else add_header_type_decl acc name fields
            | _ -> return acc))
  in
  let lookup_header_type header_type =
    String.Map.find header_type_decls header_type
    |> Result.of_option
         ~error:
           (`HeaderTypeNotDeclaredError
             (Printf.sprintf "Header type '%s' was not declared." header_type))
  in
  let%bind header_table =
    List.fold decls ~init:(Ok String.Map.empty) ~f:(fun acc decl ->
        match snd decl with
        | Struct { name; fields; _ } ->
          if String.(snd name = "headers" || snd name = "metadata") then
            List.fold fields ~init:acc ~f:(fun acc_result (_, field) ->
                let%bind inner_acc = acc_result in
                match snd field.typ with
                | TypeName (BareName (_, name)) ->
                  let%map fields = lookup_header_type name in
                  String.Map.set inner_acc ~key:(snd field.name) ~data:fields
                | HeaderStack
                    { header = _, TypeName (BareName (_, name));
                      size = _, Petr4.Types.Expression.Int (_, { value; _ })
                    } ->
                  let%bind size = bigint_to_int value in
                  let%map fields = lookup_header_type name in
                  List.fold (List.range 0 size) ~init:inner_acc
                    ~f:(fun macc idx ->
                      String.Map.set macc
                        ~key:(Printf.sprintf "%s%d" (snd field.name) idx)
                        ~data:fields)
                | _ -> Error (`NotImplementedError ""))
          else acc
        | _ -> acc)
  in
  let%map standard_meta_fields = lookup_header_type "standard_metadata_t" in
  Map.set header_table ~key:"standard_metadata" ~data:standard_meta_fields

let petr4_expr_to_instance (_ : string) (header_table : Syntax.HeaderTable.t)
    (expr : Petr4.Types.Expression.t) =
  match snd expr with
  | Name (BareName (_, inst_name))
  | ExpressionMember { expr = _, Name (BareName (_, _)); name = _, inst_name }
    ->
    Syntax.HeaderTable.lookup_instance inst_name header_table
  | _ as e ->
    Error
      (`FrontendError
        (Printf.sprintf
           "Not a member expression (Frontend.expr_to_instance): %s"
           (Sexplib.Sexp.to_string_hum (Petr4.Types.Expression.sexp_of_pre_t e))))

let is_header_field_access (name : string) (expr : Petr4.Types.Expression.t) =
  match snd expr with
  | ExpressionMember
      { expr =
          _, ExpressionMember { expr = _, Name (BareName (_, member_name)); _ };
        _
      } ->
    String.(member_name = name)
  | _ -> false

let rec expr_to_term (header_table : Syntax.HeaderTable.t) (size : int)
    (expr : Petr4.Types.Expression.t) =
  match snd expr with
  | Int (_, { value; _ }) -> bigint_to_bv value size
  | ExpressionMember
      { expr = _, ExpressionMember { name = _, instance_name; _ };
        name = _, member_name
      } ->
    Syntax.(
      let%bind inst = HeaderTable.lookup_instance instance_name header_table in
      Expression.field_to_slice inst member_name 0)
  | Cast { typ = _, BitType (_, Int (_, { value; _ })); expr } -> (
    let%bind cast_size = bigint_to_int value in
    match snd expr with
    | ExpressionMember
        { expr = _, ExpressionMember { name = _, instance_name; _ };
          name = _, field_name
        } ->
      Syntax.(
        let%bind inst =
          HeaderTable.lookup_instance instance_name header_table
        in
        let%map field = Instance.get_field inst field_name in
        if field.typ < cast_size then
          let diff = cast_size - field.typ in
          Expression.(
            Concat
              (bv_s (String.make diff '0'), Expression.instance_slice 0 inst))
        else Expression.Slice (Sliceable.Instance (0, inst), 0, cast_size))
    | _ ->
      Error
        (`NotImplementedError "Not implemented (Frontend.expr_to_term - Cast)"))
  | BinaryOp { op = _, Petr4.Types.Op.Minus; args = e1, e2 } ->
    let%bind tm1 = expr_to_term header_table size e1 in
    let%map tm2 = expr_to_term header_table size e2 in
    Syntax.Expression.Minus (tm1, tm2)
  | _ as e ->
    Log.debug (fun m ->
        m "Expr: %s"
          (Sexplib.Sexp.to_string_hum (Petr4.Types.Expression.sexp_of_pre_t e)));
    Error (`NotImplementedError "Not implemented (Frontend.expr_to_term)")

let sizeof (header_table : Syntax.HeaderTable.t)
    (expr : Petr4.Types.Expression.t) =
  match snd expr with
  | ExpressionMember
      { expr = _, ExpressionMember { name = _, instance_name; _ };
        name = _, member_name
      } ->
    Syntax.(
      let%bind inst = HeaderTable.lookup_instance instance_name header_table in
      let%map field = Instance.get_field inst member_name in
      field.typ)
  | _ -> Error (`NotImplementedError "sizeof not implemented for expression.")

let rec petr4_expr_to_formula (headers_param : string)
    (header_table : Syntax.HeaderTable.t) (expr : Petr4.Types.Expression.t) =
  match snd expr with
  | True -> return Syntax.Formula.True
  | False -> return Syntax.Formula.False
  | Int _ ->
    Error (`NotImplementedError "Not implemented (Frontend.expr_to_expr - Int)")
  | String _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_expr - String)")
  | Name _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_expr - Name)")
  | ArrayAccess _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_expr - ArrayAccess)")
  | BitStringAccess _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_expr - BitStringAccess)")
  | List _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_expr - List)")
  | Record _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_expr - Record)")
  | UnaryOp { op = _, Not; arg = e } ->
    let%map e' = petr4_expr_to_formula headers_param header_table e in
    Syntax.Formula.Neg e'
  | UnaryOp _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_expr - UnaryOp)")
  | BinaryOp { op = _, Eq; args = e1, e2 } ->
    let%bind size =
      if is_header_field_access "hdr" e1 then sizeof header_table e1
      else return 0
    in
    let%bind t1 = expr_to_term header_table 0 e1 in
    let%map t2 = expr_to_term header_table size e2 in
    Syntax.Formula.Eq (BvExpr t1, BvExpr t2)
  | BinaryOp _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_expr - BinaryOp)")
  | Cast _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_expr - Cast)")
  | TypeMember _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_expr - TypeMember)")
  | ErrorMember _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_expr - ErrorMember)")
  | ExpressionMember { expr; name = _, member_name } -> (
    match member_name with
    | "isValid" ->
      let%map inst = petr4_expr_to_instance headers_param header_table expr in
      Syntax.Formula.IsValid (0, inst)
    | _ ->
      Error
        (`NotImplementedError
          "Not implemented (Frontend.expr_to_expr - ExpressionMember)"))
  | Ternary _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_expr - Ternary)")
  | FunctionCall { func = e; type_args = []; args = [] } ->
    petr4_expr_to_formula headers_param header_table e
  | FunctionCall _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_expr - FunctionCall)")
  | NamelessInstantiation _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_expr - NamelessInstantiation)")
  | Mask _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_expr - Mask)")
  | Range _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_expr - Range)")

let rec petr4_statement_to_command (headers_param_name : string)
    (header_table : Syntax.HeaderTable.t) (stmt : Petr4.Types.Statement.pre_t) =
  match stmt with
  | MethodCall
      { func = _, ExpressionMember { name; expr }; type_args = []; args = [] }
    ->
    if String.(snd name = "setValid") then
      let%map inst =
        petr4_expr_to_instance headers_param_name header_table expr
      in
      Syntax.Command.Add inst
    else
      Error
        (`NotImplementedError
          "Not implemented (Frontend.petr4_statement_to_command - MethodCall \
           [0])")
  | MethodCall { func; args; _ } -> (
    match snd func with
    | ExpressionMember { name; _ } as exprm ->
      if String.(snd name = "extract") then
        match args with
        | [ (_, arg) ] -> (
          match arg with
          | Expression
              { value =
                  ( _,
                    ExpressionMember
                      { expr = _, ExpressionMember { name = _, _inst_name; _ };
                        name
                      } )
              }
            when String.(snd name = "next") ->
            Error (`NotImplementedError "Extract into header stack")
          | Expression
              { value = _, ExpressionMember { name = _, inst_name; _ } } ->
            let%map inst =
              Syntax.HeaderTable.lookup_instance inst_name header_table
            in
            Syntax.Command.Extract inst
          | Expression
              { value =
                  ( _,
                    ArrayAccess
                      { array = _, ExpressionMember { name = _, inst_name; _ };
                        index = _, Int (_, { value; _ })
                      } )
              } ->
            Syntax.(
              let%bind array_idx = bigint_to_int value in
              let%map inst =
                HeaderTable.lookup_instance
                  (inst_name ^ string_of_int array_idx)
                  header_table
              in
              Command.Extract inst)
          | Expression _ ->
            Error
              (`NotImplementedError
                "Not implemented (Frontend.petr4_statement_to_command)")
          | _ ->
            Error (`InvalidArgumentError "TODO: Argument is not an expression"))
        | _ -> Error (`InvalidArgumentError "Invalid argument to extract")
      else if String.(snd name = "emit") then
        match args with
        | [ (_, arg) ] -> (
          match arg with
          | Expression
              { value = _, ExpressionMember { name = _, inst_name; _ } } ->
            let%map inst =
              Syntax.HeaderTable.lookup_instance inst_name header_table
            in
            Syntax.Command.If
              ( Syntax.Formula.IsValid (0, inst),
                Syntax.Command.Remit inst,
                Syntax.Command.Skip )
          | Expression _ ->
            Error
              (`NotImplementedError
                "Not implemented (Frontend.petr4_statement_to_command)")
          | _ ->
            Error
              (`InvalidArgumentError "Argument to emit is not an expression"))
        | _ -> Error (`InvalidArgumentError "Invalid argument to emit")
      else (
        Fmt.pr "%s"
          (Sexplib.Sexp.to_string_hum
             (Petr4.Types.Expression.sexp_of_pre_t exprm));
        Error
          (`FrontendError
            (Printf.sprintf "Unrecognized method call %s" (snd name))))
    | _ -> Error (`FrontendError "Method Called on a Non-member expression"))
  | Assignment { lhs = _, ExpressionMember { expr; name = _, field }; rhs } -> (
    match petr4_expr_to_instance headers_param_name header_table expr with
    | Ok inst ->
      let open Syntax in
      let%bind l, r = Instance.field_bounds inst field in
      let%map bv = expr_to_term header_table (r - l) rhs in
      Command.Assign (inst, l, r, BvExpr bv)
    | Error e -> Error e)
  | Assignment _ ->
    Error
      (`FrontendError
        "Not implemented (Frontend.petr4_statement_to_command - Assignment)")
  | DirectApplication _ ->
    Error
      (`FrontendError
        "Not implemented (Frontend.petr4_statement_to_command - \
         DirectApplication)")
  | Conditional { cond; tru; fls } ->
    let%bind expr =
      petr4_expr_to_formula headers_param_name header_table cond
    in
    let%bind tru_cmd =
      petr4_statement_to_command headers_param_name header_table (snd tru)
    in
    let%map fls_cmd =
      Option.map fls ~f:(fun (_, fls_stmt) ->
          petr4_statement_to_command headers_param_name header_table fls_stmt)
      |> Option.value ~default:(Ok Syntax.Command.Skip)
    in
    Syntax.Command.If (expr, tru_cmd, fls_cmd)
  | BlockStatement { block } ->
    block_to_command headers_param_name header_table block
  | Exit ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.petr4_statement_to_command - Exit)")
  | EmptyStatement ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.petr4_statement_to_command - EmptyStatement)")
  | Return _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.petr4_statement_to_command - Return)")
  | Switch _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.petr4_statement_to_command - Switch)")
  | DeclarationStatement _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.petr4_statement_to_command - \
         DeclarationStatement)")

and block_to_command (headers_param : string)
    (header_table : Syntax.HeaderTable.t) (block : Petr4.Types.Block.t) =
  List.fold (snd block).statements ~init:(Ok Syntax.Command.Skip)
    ~f:(fun acc_result (_, stmt) ->
      let%bind acc = acc_result in
      let%map cmd =
        petr4_statement_to_command headers_param header_table stmt
      in
      Syntax.Command.Seq (acc, cmd))

let param_name (param : string) (params : Petr4.Types.Parameter.t list) =
  List.find_map params ~f:(fun (_, { variable; _ }) ->
      Some (return (snd variable)))
  |> Option.value
       ~default:
         (Error
            (`FrontendError (Printf.sprintf "No param with name '%s'" param)))

let collect_parser_states (headers_param_name : string)
    (header_table : Syntax.HeaderTable.t)
    (states : Petr4.Types.Parser.state list) =
  let accept = ParserCfg.mk_empty_node "accept" in
  let reject = ParserCfg.mk_empty_node "reject" in
  let init : ParserCfg.CfgNode.t String.Map.t =
    String.Map.of_alist_exn [ ("accept", accept); ("reject", reject) ]
  in
  List.fold states ~init:(Ok init) ~f:(fun acc_result (_, state) ->
      let%bind acc = acc_result in
      let%map statements =
        List.filter_map state.statements ~f:(fun (_, stmt) ->
            Some
              (petr4_statement_to_command headers_param_name header_table stmt))
        |> Utils.sequence_error
      in
      Map.set acc ~key:(snd state.name)
        ~data:
          ParserCfg.CfgNode.
            { name = snd state.name;
              statements;
              successors = ParserCfg.EdgeSet.empty
            })

let build_cfg_edges (transition : Petr4.Types.Parser.transition)
    (cfg_nodes : ParserCfg.CfgNode.t String.Map.t)
    (header_table : Syntax.HeaderTable.t) =
  match snd transition with
  | Select { exprs; cases } ->
    let%bind inst, field =
      List.find_map exprs ~f:(fun (_, expr) ->
          match expr with
          | ExpressionMember { expr = hdr; name } ->
            let field_name = snd name in
            (let%bind inst_name =
               match snd hdr with
               | ExpressionMember { name; _ } -> return (snd name)
               | ArrayAccess
                   { array = _, ExpressionMember { name = _, inst_name; _ };
                     index = _, Int (_, { value; _ })
                   } ->
                 let%map array_idx = bigint_to_int value in
                 inst_name ^ string_of_int array_idx
               | _ ->
                 Error
                   (`NotImplementedError
                     "Not implemented (Frontend.build_cfg_edges - Expression)")
             in
             let%map inst =
               Syntax.HeaderTable.lookup_instance inst_name header_table
             in
             (inst, field_name))
            |> Some
          | _ -> None)
      |> Option.value
           ~default:
             (Error (`FrontendError "Could not process select expression."))
    in
    List.fold cases ~init:(Ok []) ~f:(fun edges_acc (_, { matches; next }) ->
        let next' = String.Map.find_exn cfg_nodes (snd next) in
        List.fold matches ~init:edges_acc ~f:(fun match_acc_result (_, mtch) ->
            let%bind match_acc = match_acc_result in
            let%map edge_type =
              match mtch with
              | Default -> return ParserCfg.EdgeType.Default
              | DontCare ->
                Error
                  (`NotImplementedError
                    "Not implemented (Frontend.build_cfg_edges - DontCare)")
              | Expression { expr = _, Int n } ->
                return (ParserCfg.EdgeType.Match (inst, field, (snd n).value))
              | Expression { expr = _ } ->
                Error
                  (`NotImplementedError
                    "Not implemented (Frontend.build_cfg_edges - Expression)")
            in
            let edge = ParserCfg.Edge.{ node = next'; typ = edge_type } in
            edge :: match_acc))
  | Direct { next } ->
    let%map next =
      String.Map.find cfg_nodes (snd next)
      |> Result.of_option ~error:(`FrontendError "Next node not found.")
    in
    [ ParserCfg.Edge.{ node = next; typ = ParserCfg.EdgeType.Default } ]

let build_parser_cfg (header_table : Syntax.HeaderTable.t)
    (parser_states : Petr4.Types.Parser.state list)
    (parser_params : Petr4.Types.Parameter.t list) =
  let%bind headers_param_name = param_name "headers" parser_params in
  let%bind cfg_nodes =
    collect_parser_states headers_param_name header_table parser_states
  in
  Logs.debug (fun m ->
      m "CFG Nodes: %s"
        (Sexplib.Sexp.to_string_hum
           (String.Map.sexp_of_t ParserCfg.CfgNode.sexp_of_t cfg_nodes)));
  List.fold parser_states ~init:(Ok cfg_nodes) ~f:(fun acc_result (_, state) ->
      let%bind acc = acc_result in
      let node_name = snd state.name in
      let node = String.Map.find_exn acc node_name in
      let%map edges = build_cfg_edges state.transition cfg_nodes header_table in
      let edge_set =
        List.fold edges ~init:node.successors ~f:(fun acc edge ->
            ParserCfg.EdgeSet.add acc edge)
      in
      String.Map.set acc ~key:node_name
        ~data:{ node with successors = edge_set })

let parser_cfg_to_command (cfg : ParserCfg.CfgNode.t String.Map.t) =
  let%bind start =
    String.Map.find cfg "start"
    |> Result.of_option
         ~error:(`FrontendError "CFG does not contain state 'start'.")
  in
  let rec traverse_nodes (state : ParserCfg.CfgNode.t) =
    let stmts_cmd =
      List.fold state.statements ~init:Syntax.Command.Skip ~f:(fun acc stmt ->
          Syntax.Command.Seq (stmt, acc))
    in
    if Set.is_empty state.successors then return stmts_cmd
    else
      let default, successors =
        Set.partition_tf state.successors ~f:(fun edge ->
            match edge.typ with
            | ParserCfg.EdgeType.Default -> true
            | _ -> false)
      in
      let%bind default_edge =
        Result.of_option (Set.nth default 0)
          ~error:(`FrontendError "Default successor is missing.")
      in
      let default_cmd =
        match default_edge.node with
        | { name = "accept"; _ } ->
          if Set.is_empty successors then return stmts_cmd
          else return Syntax.Command.Skip
        | { name = "reject"; _ } ->
          Error (`FrontendError "Don't know how to handle reject.")
        | next ->
          let%bind node =
            String.Map.find cfg next.name
            |> Result.of_option
                 ~error:(`FrontendError "Could not lookup node from CFG.")
          in
          let%bind acc = traverse_nodes node in
          Ok (Syntax.Command.Seq (stmts_cmd, acc))
      in
      if Set.is_empty successors then default_cmd
      else
        let%map succ_cmd =
          Set.fold successors ~init:default_cmd ~f:(fun acc_result edge ->
              let%bind acc = acc_result in
              match edge.typ with
              | ParserCfg.EdgeType.Default ->
                Error
                  (`FrontendError
                    "Default edges should have been filtered out at this point.")
              | ParserCfg.EdgeType.Match (inst, field, value) ->
                let%bind slice =
                  Syntax.Expression.field_to_slice inst field 0
                in
                let%bind inst_field = Syntax.Instance.get_field inst field in
                let%bind bv = bigint_to_bv value inst_field.typ in
                let expr = Syntax.(Formula.Eq (BvExpr slice, BvExpr bv)) in
                let%bind node =
                  String.Map.find cfg edge.node.name
                  |> Result.of_option
                       ~error:(`FrontendError "Could not lookup node from CFG.")
                in
                let%map cmd = traverse_nodes node in
                Syntax.Command.If (expr, cmd, acc))
        in
        Syntax.Command.Seq (stmts_cmd, succ_cmd)
  in
  let%map result = traverse_nodes start in
  Simplify.simplify_command result

let parser_to_command header_table parser_states parser_params =
  let%bind parser_cfg =
    build_parser_cfg header_table parser_states parser_params
  in
  parser_cfg_to_command parser_cfg

let control_to_command (header_table : Syntax.HeaderTable.t)
    (control_apply : Petr4.Types.Block.t)
    (control_params : Petr4.Types.Parameter.t list) =
  let%bind headers_param_name = param_name "headers" control_params in
  let%map cmd =
    block_to_command headers_param_name header_table control_apply
  in
  Simplify.simplify_command cmd

let extract_annotation_body (header_table : Syntax.HeaderTable.t)
    (annotation : Petr4.Types.Annotation.pre_t) =
  match snd annotation.body with
  | Petr4.Types.Annotation.Unparsed (body :: _) ->
    let body =
      String.chop_prefix_if_exists
        (String.chop_suffix_if_exists (snd body) ~suffix:"\"")
        ~prefix:"\""
    in
    Log.debug (fun m -> m "Annotation body: %s" body);
    let%map annotation = Parsing.parse_annotation header_table body in
    Some annotation
  | _ -> return None

let find_pi4_annotations (header_table : Syntax.HeaderTable.t)
    (annotations : Petr4.Types.Annotation.t list) =
  List.fold annotations ~init:[] ~f:(fun acc (_, annotation) ->
      match snd annotation.name with
      | "pi4" -> (
        match extract_annotation_body header_table annotation with
        | Ok pi4_annotation ->
          Option.map pi4_annotation ~f:(fun annot -> annot :: acc)
          |> Option.value ~default:acc
        | Error (`SyntaxError e) ->
          Log.err (fun m -> m "Failed to parse annotation with error %s" e);
          acc)
      | _ -> acc)

let collect_annotations (header_table : Syntax.HeaderTable.t)
    (Petr4.Types.Program decls) =
  List.fold decls ~init:[] ~f:(fun acc decl ->
      match snd decl with
      | Control { annotations; _ }
      | Parser { annotations; _ }
      | Struct { annotations; _ }
      | Header { annotations; _ } ->
        find_pi4_annotations header_table annotations @ acc
      | _ -> acc)

let declaration_to_command (header_table : Syntax.HeaderTable.t)
    (decls : Petr4.Types.Declaration.t list) (name : string) =
  List.find_map decls ~f:(fun decl ->
      match snd decl with
      | Parser { name = n; states; params; _ } when String.(snd n = name) ->
        let parser_cmd = parser_to_command header_table states params in
        Some parser_cmd
      | Control { name = n; apply; params; _ } when String.(snd n = name) ->
        Some (control_to_command header_table apply params)
      | _ -> None)
  |> Option.value
       ~default:
         (Error
            (`FrontendError
              (Fmt.str "No declaration with name '%s' found." name)))

let rec annotation_body_to_command (header_table : Syntax.HeaderTable.t)
    (decls : Petr4.Types.Declaration.t list)
    (annotation_body : Syntax.Annotation.annotation_body) =
  match annotation_body with
  | Reset -> return Syntax.Command.Reset
  | Block _name -> declaration_to_command header_table decls _name
  | TypedBlock (body, typ) -> (
    let%map body_cmd = annotation_body_to_command header_table decls body in
    match typ with
    | Pi (binder, input, output) ->
      Syntax.Command.Ascription (body_cmd, binder, input, output))
  | Sequence (l, r) ->
    let%bind l_cmd = annotation_body_to_command header_table decls l in
    let%map r_cmd = annotation_body_to_command header_table decls r in
    Syntax.Command.Seq (l_cmd, r_cmd)

let annotation_to_command (header_table : Syntax.HeaderTable.t)
    (decls : Petr4.Types.Declaration.t list) (annotation : Syntax.Annotation.t)
    =
  match annotation with
  | TypeAnnotation (body, _) ->
    annotation_body_to_command header_table decls body
