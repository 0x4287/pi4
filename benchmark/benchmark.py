import subprocess
import pandas as pd

rounds = 10

clear_line = '                                         '
programs = [
    'tut_basic',
    'tut_basic_tunnel',
    'tut_load_balance',
    # 'determined_forwarding',
    # 'header_dependency',
    # 'ipv4_opt',
    # 'ipv4_ttl',
    # 'mutual_exclusion_ingress',
    # 'roundtripping',
    # 'vlan_decap'
]

suffixes = [
    '_safe',
    '_unsafe'
]

flags = [
    [],
    ['-f'],
    ['-i'],
    ['-n'],
    ['-f', '-i', '-n']
]

out_file = './results.csv'

results = pd.DataFrame({'program': [], 'flags': [], 'runtime': []})

for prog in programs:
    for suf in suffixes:
        for flag in flags:
            for i in range(rounds):
                print(
                    'Running: ' + prog + suf + ' ' + ' '.join(flag) +
                    ' [' + str(i + 1) + '/' + str(rounds) + ']')
                rslt = subprocess.run([
                                          '../_build/default/benchmark/benchmark.exe',
                                          './programs/' + prog + suf + '.pi4',
                                          '-t', './programs/' + prog + suf + '.pi4_type']
                                      + flag,
                                      stdout=subprocess.PIPE,
                                      text=True)
                print(rslt.stdout.strip())
                results = results.append(
                    pd.DataFrame(
                        {'program': [prog + suf], 'flags': [' '.join(flag)], 'runtime': [rslt.stdout.strip()]}),
                    ignore_index=True)

results.to_csv(out_file)
