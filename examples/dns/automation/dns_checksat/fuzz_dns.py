import subprocess
import re

num_iterations = 50

cvc5_bin = "/Users/lorchrob/Documents/CodeProjects/grammar-based_fuzzing/SyGuS-fuzzing/CVC4/build/bin/cvc5"
sygus_file = "../../checksat/dns_monolithic_checksat.smt2"  
temp_file = "../../checksat/dns_monolithic_checksat_temp.smt2" 
command = f"{cvc5_bin} {temp_file} --produce-models --incremental"  

subprocess.run(f"cp {sygus_file} {temp_file}", shell=True, capture_output=True, text=True)

def call_command_and_append_to_file(command, output_file):
  with open(output_file, 'a') as f:
    result = subprocess.run(command, shell=True, capture_output=True, text=True)
    pattern = r"sat\n\(\n\(define-fun dns_message \(\) DNSMessage (.+)\)\n\)"
    result = re.findall(pattern, result.stdout)[-1]
    result = f"\n(assert (not (= dns_message {result})))\n(check-sat)\n(get-model)\n"
    f.write(result)

for _ in range(num_iterations):
  call_command_and_append_to_file(command, temp_file)