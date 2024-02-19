(* Write function to call the given terminal command a given number of times 
   and write to the given output file*)

let gen_terms (num_calls : int) (smt_filename : string) (smt_temp_filename : string) (output_filename : string) = 
  let _ = Sys.command ("cp " ^ smt_filename ^ " " ^ smt_temp_filename) in
  let channel = open_out_gen [Open_append] 0o666 smt_temp_filename in 

  let check_synth_command = "(check-synth)\n" in 
  for _ = 1 to num_calls do
    output_string channel check_synth_command;
  done;
  close_out channel;

  let sygus_command_prefix = "/Users/lorchrob/Documents/CodeProjects/grammar-based_fuzzing/SyGuS-fuzzing/CVC4/build/bin/cvc5 --lang=sygus2" in
  let sygus_command = sygus_command_prefix ^ " " ^ smt_temp_filename ^ " > " ^ output_filename in 

  let _ = Sys.command sygus_command in 
  let _ = Sys.command ("rm " ^ smt_temp_filename) in 
  ()

let main () = 
  let _ = gen_terms 50 "../../dns/abstract_partition/dns_base.smt2" 
                       "../../dns/abstract_partition/dns_base_temp.smt2"
                       "../../results/dns_base_output.txt" in
  let _ = gen_terms 50 "../../dns/abstract_partition/dns_domain_name.smt2" 
                       "../../dns/abstract_partition/dns_domain_name_temp.smt2" 
                       "../../results/dns_domain_name_output.txt" in
  let _ = gen_terms 50 "../../dns/abstract_partition/dns_rdata_v2.smt2" 
                       "../../dns/abstract_partition/dns_rdata_v2_temp.smt2" 
                       "../../results/dns_rdata_output.txt" in
  let _ = gen_terms 50 "../../dns/abstract_partition/dns_ttl.smt2" 
                       "../../dns/abstract_partition/dns_ttl_temp.smt2"
                       "../../results/dns_ttl_output.txt" in



  let _ = gen_terms 50 "../../dns/abstract_partition/dns_monolithic.smt2" 
                       "../../dns/abstract_partition/dns_monolithic_temp.smt2" 
                       "../../results/dns_rdata_output.txt" in
          ()