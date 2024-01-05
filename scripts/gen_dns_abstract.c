#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const char *sygus_command_prefix = "/Users/lorchrob/Documents/CodeProjects/grammar-based_fuzzing/SyGuS-fuzzing/CVC4/build/bin/cvc5 --lang=sygus2";

// Given a sygus command prefix, a sygus file to call, and an output file,
// construct a sygus terminal command
char *build_sygus_command(const char *str1, const char *str2, const char *str3) {
    size_t len = strlen(str1) + strlen(str2) + strlen(str3) + 5;
    char* result = (char*) malloc(len + 1);

    if (result == NULL) {
        fprintf(stderr, "Memory allocation error\n");
        exit(EXIT_FAILURE);
    }

    snprintf(result, len + 1, "%s %s > %s", str1, str2, str3);
    printf("Sygus command: %s\n", result);
    return result;
}

// Copy file at directory 'input_filename' to a f
void copy_file(const char *source, const char *destination) {
    // Construct the cp command
    char command[1024];
    snprintf(command, sizeof(command), "cp %s %s", source, destination);

    // Execute the cp command
    int result = system(command);
    if (result == -1) {
        perror("Error executing cp command");
        exit(EXIT_FAILURE);
    }
}

// Call a given number of check-synths on the given sygus file
// and save the results
int gen_terms(int iterations, const char *sygus_file_dir, const char *sygus_file_dir_temp, const char *output_dir) {
    copy_file(sygus_file_dir, sygus_file_dir_temp);

    FILE *sygus_file_temp = fopen(sygus_file_dir_temp, "a");
    if (sygus_file_temp == NULL) {
        perror("Error opening file");
        return 1;
    }

    // Append check-synth commands to the sygus file
    for (int i = 0; i < iterations; ++i) {
        fprintf(sygus_file_temp, "(check-synth)\n");
    }
    printf("Successfully appended check-synth commands to %s\n", sygus_file_dir_temp);
    fclose(sygus_file_temp);

    // Execute sygus and save its output to a file
    char* sygus_command = build_sygus_command(sygus_command_prefix, sygus_file_dir_temp, output_dir);
    int result = system(sygus_command);

    if (result == -1) {
        perror("Error executing sygus");
        return 1;
    } else {
        printf("Sygus command executed successfully.\n\n");
    }

    return 0;
}

int main() {
    gen_terms(10, "../dns/abstract_partition/dns_base.smt2", "../dns/abstract_partition/dns_base_temp.smt2", "./dns_base_output.txt");
    gen_terms(10, "../dns/abstract_partition/dns_domain_name.smt2", "../dns/abstract_partition/dns_domain_name_temp.smt2", "./dns_domain_name_output.txt");
    gen_terms(10, "../dns/abstract_partition/dns_rdata.smt2", "../dns/abstract_partition/dns_rdata_temp.smt2", "./dns_rdata_output.txt");

    return 0;
}
