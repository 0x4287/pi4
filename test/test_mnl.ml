open Alcotest
open Pi4
open Syntax

let ipv4_inst =
 Test_utils.mk_inst "ipv4" 
 [
  ("ihl", 2);
  ("ttl", 4);
  ("flg", 2) 
]
let header_table = HeaderTable.populate [ ipv4_inst]

module TestConfig = struct
 let verbose = true
 let maxlen = ref(10)
end

module Test = Test_utils.TestRunner (TestConfig)

let test1 () =
 let input =
   Parsing.parse_heap_type header_table []
     {| 
     {y: ⊤ | y.pkt_in.length > 8}
     |}
 in

 let hty =
   Parsing.parse_heap_type header_table
     [ ("x", Env.VarBind input) ]
     {| 
     {y':
     ⊤
     | (y'.ipv4.valid ∧
     (y'.ipv4[0:8] == x.pkt_in[0:2]@(x.pkt_in[2:6] - 0b0001)@x.pkt_in[6:8] ∧
     ((y'.pkt_in.length + 8) == x.pkt_in.length ∧
     (x.pkt_in[0:8]@y'.pkt_in == x.pkt_in ∧
     (y'.pkt_out == x.pkt_out@x.pkt_in[0:2]@(x.pkt_in[2:6] - 0b0001)@x.pkt_in[6:8] ∧
     y'.pkt_out.length == (x.pkt_out.length + 8))))))}
    |}
 in

 let hty_smpl =
   Parsing.parse_heap_type header_table
     [ ("x", Env.VarBind input) ]
     {|
      {y: ⊤ | 
        y.ipv4.valid ∧
        y.ipv4[0:8] == x.pkt_in[0:2]@(x.pkt_in[2:6] - 0b0001)@x.pkt_in[6:8] ∧
        (y.pkt_in.length + 8) == x.pkt_in.length ∧
        x.pkt_in[0:8]@y.pkt_in == x.pkt_in ∧
        y.pkt_out == x.pkt_out@x.pkt_in[0:2]@(x.pkt_in[2:6] - 0b0001)@x.pkt_in[6:8] ∧
        y.pkt_out.length == (x.pkt_out.length + 8)
      }
     |}
 in
 Test.is_equiv hty_smpl hty [ ("x", Env.VarBind input) ] header_table

let test2 () =
  let input =
    Parsing.parse_heap_type header_table []
      {| 
      {y: ⊤ | y.pkt_in.length > 8}
      |}
  in

  let hty =
    Parsing.parse_heap_type header_table
      [ ("x", Env.VarBind input) ]
      {| 
      {y':
      ⊤
      | (y'.ipv4.valid ∧
      (y'.ipv4[0:8] == x.pkt_in[0:2]@(x.pkt_in[2:6])@x.pkt_in[6:8] ∧
      ((y'.pkt_in.length + 8) == x.pkt_in.length ∧
      (x.pkt_in[0:8]@y'.pkt_in == x.pkt_in ∧
      (y'.pkt_out == x.pkt_out@x.pkt_in[0:2]@(x.pkt_in[2:6])@x.pkt_in[6:8] ∧
      y'.pkt_out.length == (x.pkt_out.length + 8))))))}
      |}
  in

  let hty_smpl =
    Parsing.parse_heap_type header_table
      [ ("x", Env.VarBind input) ]
      {|
        {y: ⊤ | 
          y.ipv4.valid ∧
          y.ipv4[0:8] == x.pkt_in[0:2]@(x.pkt_in[2:6])@x.pkt_in[6:8] ∧
          (y.pkt_in.length + 8) == x.pkt_in.length ∧
          x.pkt_in[0:8]@y.pkt_in == x.pkt_in ∧
          y.pkt_out == x.pkt_out@x.pkt_in[0:2]@(x.pkt_in[2:6])@x.pkt_in[6:8] ∧
          y.pkt_out.length == (x.pkt_out.length + 8)
        }
      |}
  in
  Test.is_equiv hty_smpl hty [ ("x", Env.VarBind input) ] header_table

let test_set = 
  [ test_case "Test 1" `Quick test1; 
    test_case "Test 2" `Quick test2  ]
