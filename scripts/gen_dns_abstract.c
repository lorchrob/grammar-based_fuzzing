#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const char *sygus_command_prefix = "/Users/lorchrob/Documents/CodeProjects/grammar-based_fuzzing/SyGuS-fuzzing/CVC4/build/bin/cvc5 --lang=sygus2";

// Remove unneeded lines with single parens from sygus output
void clean_output_file(char* filename) {
    FILE* inputFile = fopen(filename, "r");
    FILE* tempFile = fopen("temp.txt", "w");

    if (inputFile == NULL || tempFile == NULL) {
        perror("Error opening files");
        exit(EXIT_FAILURE);
    }

    char buffer[256];

    while (fgets(buffer, sizeof(buffer), inputFile)) {
        // Remove newline character
        buffer[strcspn(buffer, "\n")] = '\0';

        // Check if the line is only a single character long
        if (strlen(buffer) > 1) {
            // Remove instances of a given keyword
            // char* occurrence = strstr(buffer, "DNSMessage");
            // while (occurrence != NULL) {
            //     *occurrence = ' '; // Replace with a space
            //     occurrence = strstr(buffer, "DNSMessage");
            // }

            fprintf(tempFile, "%s\n", buffer);
        }
    }

    fclose(inputFile);
    fclose(tempFile);

    remove(filename);
    rename("temp.txt", filename);
}

// Delete file (used to clean up generated temp files)
int delete_file(const char *filename) {
    if (remove(filename) == 0) {
        printf("Sygus file '%s' deleted successfully.\n\n", filename);
        return 0;
    } else {
        perror("Error deleting file");
        return 1; 
    }
}

// Copy file 'source' to new file 'dest' (used to generate temp files)
void copy_file(const char *source, const char *destination) {
    char command[1024];
    snprintf(command, sizeof(command), "cp %s %s", source, destination);

    int result = system(command);
    if (result == -1) {
        perror("Error executing cp command");
        exit(EXIT_FAILURE);
    }
}

// Given a sygus command prefix, a sygus file to call, and an output file,
// construct a sygus terminal command
const char *build_sygus_command(const char *str1, const char *str2, const char *str3) {
    size_t len = strlen(str1) + strlen(str2) + strlen(str3) + 5;
    char *result = (char*) malloc(len + 1);

    if (result == NULL) {
        fprintf(stderr, "Memory allocation error\n");
        exit(EXIT_FAILURE);
    }

    snprintf(result, len + 1, "%s %s > %s", str1, str2, str3);
    printf("Sygus command: %s\n", result);
    return result;
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
    const char* sygus_command = build_sygus_command(sygus_command_prefix, sygus_file_dir_temp, output_dir);
    int result = system(sygus_command);

    if (result == -1) {
        perror("Error executing sygus\n");
        return 1;
    } else {
        printf("Sygus command executed successfully.\n");
    }

    delete_file(sygus_file_dir_temp);

    return 0;
}

int main() {
    gen_terms(
        50, 
        "../dns/abstract_partition/dns_base.smt2", 
        "../dns/abstract_partition/dns_base_temp.smt2", 
        "./results/dns_base_output.txt"
    );
    gen_terms(
        50, 
        "../dns/abstract_partition/dns_domain_name.smt2", 
        "../dns/abstract_partition/dns_domain_name_temp.smt2", 
        "./results/dns_domain_name_output.txt"
    );
    gen_terms(
        50, 
        "../dns/abstract_partition/dns_rdata_v2.smt2", 
        "../dns/abstract_partition/dns_rdata_temp.smt2", 
        "./results/dns_rdata_output.txt"
    );

    clean_output_file("results/dns_base_output.txt");
    clean_output_file("results/dns_domain_name_output.txt");
    clean_output_file("results/dns_rdata_output.txt");


    return 0;
}
