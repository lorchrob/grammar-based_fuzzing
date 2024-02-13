import re

def remove_let_def(input_text):
    output_text = ""
    let_count = 0
    in_let = False

    for i, char in enumerate(input_text): 
        if len(output_text) >= 4 and output_text[i-4:i] == "(let":
            let_count += 1
            output_text = output_text[0:i-5]
            in_let = True
            let_count = 1
            
        if in_let:
            if char == "(":
                let_count += 1
            elif char == ")":
                let_count -= 1
                if let_count == 1:
                    in_let = False
        else:
            output_text += char
        
    if let_count > 0:
        output_text = output_text[0:-let_count]
        
    return output_text

def inline_let(line):
    # Regular expression to match let bindings
    inner_let_pattern = r'(_let_\d)+ \((.*?)\)'
    matches = re.findall(inner_let_pattern, line)
    
    print('----------------')
    print(line)
    # Remove let binding definitions
    line_new = remove_let_def(line)
    print(line_new)
    while line_new != line:
        line = line_new
        line_new = remove_let_def(line_new)
        print(line_new)
    line = line_new

    # Replace variables with their let bound definitions
    line_new = " " + line
    while line_new != line:
        line = line_new
        for variable, definition in matches:
            print(variable + ", " + definition)
            line_new = line_new.replace(variable, "(" + definition + ")")
            print(line_new)
    print('----------------')
    
    return line

def main():
    input_filename = '../results/dns_rdata_output.txt'
    output_filename = '../results/dns_rdata_output_clean.txt'

    with open(input_filename, 'r') as input_file, open(output_filename, 'w') as output_file:
        for line in input_file:
            line = line.strip()
            if line:
                line = inline_let(line)
                line = line.replace("define-fun dns_rdata () DNSRDATA ", "")
                line = line[2:-1] # Remove extra parens
                output_file.write(f"{line}\n")
                
    input_filename = '../results/dns_domain_name_output.txt'
    output_filename = '../results/dns_domain_name_output_clean.txt'

    with open(input_filename, 'r') as input_file, open(output_filename, 'w') as output_file:
        for line in input_file:
            line = line.strip()
            if line:
                line = inline_let(line)
                line = line.replace("define-fun domain_name () Top ", "")
                line = line[2:-1] # Remove extra parens
                output_file.write(f"{line}\n")
            
    input_filename = '../results/dns_ttl_output.txt'
    output_filename = '../results/dns_ttl_output_clean.txt'

    with open(input_filename, 'r') as input_file, open(output_filename, 'w') as output_file:
        for line in input_file:
            line = line.strip()
            if line:
                line = inline_let(line)
                line = line.replace("define-fun dns_packet () Top ", "")
                line = line[2:-1] # Remove extra parens
                output_file.write(f"{line}\n")
                
    input_filename = '../results/dns_base_output.txt'
    output_filename = '../results/dns_base_output_clean.txt'

    with open(input_filename, 'r') as input_file, open(output_filename, 'w') as output_file:
        for line in input_file:
            line = line.strip()
            if line:
                line = inline_let(line)
                output_file.write(f"{line}\n")

if __name__ == "__main__":
    definitions = {}
    main()
