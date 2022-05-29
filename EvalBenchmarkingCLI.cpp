// Small program to imitate MaxSATEvaluations' results summary.
// Calls EvalMaxSAT on files in unweighted_data.h across multiple threads while dealing with timeouts.

#include <iostream>
#include <cstdio>
#include <memory>
#include <stdexcept>
#include <string>
#include <array>
#include <sys/stat.h>
#include <sstream>
#include <limits>
#include <thread>
#include <fstream>
#include <unistd.h>
#include <mutex>
#include <zlib.h>

#include "unweighted_data.h"
#include "weighted_data.h"
#include "lib/CLI11.hpp"
#include "lib/EvalMaxSAT/src/ParseUtils.h"
#include "config.h"

// g++ EvalBenchmarking.cpp -o EvalBenchmarking -lpthread -lz
// Warning : if you interrupt the process, the threads will keep going as I didn't handle that case

// !!! Modify the following args !!!
std::string MAXSAT_BIN_PATH = "./EvalMaxSAT_bin";
std::string OUTPUT_FILE = "bench.txt";
std::string BENCHMARK_TIMEOUT = "3600"; // In seconds
int NUMBER_OF_THREADS = 1;
bool weighted_dataset=false;
// #################################

static std::mutex forPrint;
    
std::vector<int> instancesPerThreads;
std::vector<long double> timePerThread;
std::vector<int> timeoutPerThread;
std::vector<std::vector<std::string>> threadResults;
std::vector<std::thread> benchmarkThreads;
int benchmarksNotFound = 0; // Not thread-safe to use a simple int here but rarely used so wtv


namespace  {
    void _toString(std::ostringstream &oss){
    }

    template<typename T1, typename ...T>
    void _toString(std::ostringstream &oss, const T1& arg, const T&... args) {
        oss << arg;
        _toString(oss, args...);
    }
}


template<typename ...T>
std::string toString(const T&... args) {
    std::ostringstream oss;
    _toString(oss, args...);
    return oss.str();
}

std::string exec(const char* cmd) {
    std::array<char, 128> buffer;
    std::string result;
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd, "r"), pclose);
    if (!pipe) {
        throw std::runtime_error("popen() failed!");
    }
    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        result += buffer.data();
    }
    return result;
}

inline bool file_exists (const std::string& name) {
    struct stat buffer;
    return (stat (name.c_str(), &buffer) == 0);
}


template<class B>
static void readClause(B& in, std::vector<int>& lits) {
    int parsed_lit;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        lits.push_back( parsed_lit );
    }
}

unsigned long long calculateCost(const std::string & file, const std::vector<bool> &result) {
    unsigned long long cost = 0;
    auto in_ = gzopen(file.c_str(), "rb");
    unsigned long long weightForHardClause = -1;

    StreamBuffer in(in_);

    std::vector<int> lits;
    for(;;) {
        skipWhitespace(in);

        if(*in == EOF)
            break;

        else if(*in == 'c') {
            skipLine(in);
        } else if(*in == 'p') { // Old format
          ++in;
          if(*in != ' ') {
              std::cerr << "o PARSE ERROR! Unexpected char: " << static_cast<char>(*in) << std::endl;
              return false;
          }
          skipWhitespace(in);

          if(eagerMatch(in, "wcnf")) {
              parseInt(in); // # Var
              parseInt(in); // # Clauses
              weightForHardClause = parseWeight(in);
          } else {
              std::cerr << "o PARSE ERROR! Unexpected char: " << static_cast<char>(*in) << std::endl;
              return false;
          }
      }
        else {
            unsigned long long weight = parseWeight(in);
            readClause(in, lits);
            if(weight == weightForHardClause) {
                bool sat=false;
                for(auto l: lits) {
                    if(abs(l) >= result.size()) {
                        std::cerr << "calculateCost: Parsing error." << std::endl;
                        return -1;
                    }
                    if ( (l>0) == (result[abs(l)]) ) {
                        sat = true;
                        break;
                    }
                }
                if(!sat) {
                    std::cerr << "calculateCost: NON SAT !" << std::endl;
                    return -1;
                }
            } else {
                bool sat=false;
                for(auto l: lits) {
                    if(abs(l) >= result.size()) {
                        std::cerr << "calculateCost: Parsing error." << std::endl;
                        return -1;
                    }

                    if ( (l>0) == (result[abs(l)]) ) {
                        sat = true;
                        break;
                    }
                }
                if(!sat) {
                    cost += weight;
                }
            }
        }
    }

    gzclose(in_);
    return cost;
}


std::string parse_result(std::string path, long long unsigned trueCost, std::string result, int threadNumber) {
    long long unsigned cost;
    std::vector<bool> values;

    std::istringstream issResult(result);
    std::string line;
    std::string res;
    std::string output;
    while (std::getline(issResult, line))
    {
        std::istringstream iss(line);
        char action;
        if(!(iss >> action)) {
            continue;
        }
        switch (action) {

        case 'c':
        {
            std::string temp;
            iss >> temp;
            if (temp != "Total") continue;

            iss >> temp;
            if (temp != "time:") continue;

            iss >> temp; // Time
            long double time = std::stod(temp);
            iss >> temp; // Time unit
            if (temp == "ms")
                time /= 1000;
            if (temp == "µs")
                time /= 1000000;
            timePerThread[threadNumber] += time;
            output = std::to_string(time);

            return output;
        }

        case 'o':
        {
            if(!(iss >> cost)) { // Getting the cost
                {std::lock_guard lock(forPrint); std::cerr << "Parsing error. line: " << line << std::endl;}
                return "-1";
            }

            if(cost != trueCost) {
                {std::lock_guard lock(forPrint); std::cerr << "Error cost: Find = " << cost << ", Inspected = " << trueCost << std::endl;}
                return "-1";
            }

            output = std::to_string(cost);



            break;
        }

        case 's':
        {
            if(!(iss >> res)) {
                {std::lock_guard lock(forPrint); std::cerr << "Parsing error. line: " << line << std::endl;}
                return "-1";
            }
            if( (res.compare("OPTIMUM") != 0) && (res.compare("SATISFIABLE") != 0) ) {
                {std::lock_guard lock(forPrint); std::cerr << "No solution. line: " << line << std::endl;}
                return "-1";
            }
            break;
        }

        case 'v':
        {
            if(!(iss >> res)) {
                {std::lock_guard lock(forPrint); std::cerr << "Parsing error. line: " << line << std::endl;}
                return "-1";
            }

            values.push_back(0); // fake lit

            int res2;
            if(!(iss >> res2)) {
                if(res.compare("-1") ==  0) {
                    res = "0"; // special case of a single variable
                }

                // New format
                for(unsigned int i=0; i<res.size(); i++) {
                    values.push_back(res[i] == '1');
                }
            } else {
                // Old format
                int lit = std::atoi(res.c_str());
                values.push_back(lit > 0);
                if( (values.size()-1) != abs(lit) ) {
                    {std::lock_guard lock(forPrint); std::cerr << "Parsing error. line: " << line << std::endl;}
                    return "-1";
                }

                values.push_back(res2 > 0);

                while(iss>>lit) {
                    values.push_back(lit > 0);
                    if((values.size()-1) != abs(lit)) {
                        {std::lock_guard lock(forPrint); std::cerr << "Parsing error. line: " << line << std::endl;}
                        return "-1";
                    }
                }
            }

            long long unsigned computedCost = calculateCost(path, values);


            if(cost != computedCost) {
                {std::lock_guard lock(forPrint); std::cerr << "Error cost: Retourned cost = " << cost << ", Computed cost = " << computedCost << std::endl;}
                return "-1";
            }

            break;
        }

        default:
            {std::lock_guard lock(forPrint); std::cerr << "Parsing error. line: " << line << std::endl;}
            return "-1";
        }
    }
    return "-1";
}


void run_benchmark( int threadNumber) {
    int startIndex = 0;
    for (int i = 0; i < threadNumber; i++)
        startIndex += instancesPerThreads[i];

    int resultIndex = 0;
    for (int i = startIndex; i < startIndex + instancesPerThreads[threadNumber] - 1; i++, resultIndex++) {
        std::string path = (weighted_dataset?BENCHMARK_FILES_FOLDER_WEIGHTED:BENCHMARK_FILES_FOLDER_UNWEIGHTED) + (weighted_dataset?data_weighted[i]:data_unweighted[i]);

        if (!file_exists(path))
        {
            {std::lock_guard lock(forPrint);std::cerr << "The following file, at index " << i << ", does not exist : " << std::endl << path << std::endl;}
            benchmarksNotFound++;
            continue;
        }
        std::string cmdString = "timeout " + BENCHMARK_TIMEOUT + " " + MAXSAT_BIN_PATH + " " + path + " 2> /dev/null";
        const char* cmdChar = cmdString.c_str();
	
        std::string result = exec(cmdChar);
        if (result == "c Interrupt signal (15) received.\n")
        {
            result = BENCHMARK_TIMEOUT + "\t" + (weighted_dataset?data_weighted[i]:data_unweighted[i]);
            timeoutPerThread[threadNumber]++;
        }
        else
        {
            std::string parsedResult = parse_result( path, (weighted_dataset?data_weighted_cost[i]:data_unweighted_cost[i]), result, threadNumber );
            if (parsedResult == "-1") {
                {std::lock_guard lock(forPrint);std::cerr << "Parsing error in " << path << " (caused by timeout). Skipping file." << std::endl;}
                benchmarksNotFound++;
                continue;
            }
            result = parsedResult + "\t" + (weighted_dataset?data_weighted[i]:data_unweighted[i]);
        }
        threadResults[ threadNumber ][ resultIndex ] = result;
        {std::lock_guard lock(forPrint);std::cout << result << std::endl;}
    }
}



int main(int argc, char *argv[]) {

    CLI::App app{"EvalMaxSAT Chenchmarking CLI"};
    
    app.add_option("bin_path", MAXSAT_BIN_PATH, "MAXSAT binary path")->check(CLI::ExistingFile)->required();
    
    //app.add_option("benchmark_files_folder", BENCHMARK_FILES_FOLDER, "Benchmark files folder")->check(CLI::ExistingDirectory)->required();
    
    app.add_option("-o", OUTPUT_FILE, "output (defaut = bench.txt)");

    app.add_flag("-w", weighted_dataset, "Use a weighted dataset (default = unweighted dataset).");
    
    app.add_option("-p", NUMBER_OF_THREADS, toString("Number of threads (default = ", NUMBER_OF_THREADS,")"));
    
    app.add_option("--timeout", BENCHMARK_TIMEOUT, toString("Timeout in second (default = ",BENCHMARK_TIMEOUT,")"));

	
    CLI11_PARSE(app, argc, argv);

    std::cout << "TIME (sec)\tFILE" << std::endl;

    instancesPerThreads.resize(NUMBER_OF_THREADS);
    threadResults.resize(NUMBER_OF_THREADS);
    timePerThread.resize( NUMBER_OF_THREADS);
    timeoutPerThread.resize(NUMBER_OF_THREADS);
    benchmarkThreads.reserve(NUMBER_OF_THREADS);

    int generalNumberOfInstances = (weighted_dataset?data_weighted.size():data_unweighted.size()) / NUMBER_OF_THREADS;
    int rest = (weighted_dataset?data_weighted.size():data_unweighted.size()) % NUMBER_OF_THREADS;

    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
        timePerThread[i] = 0; timeoutPerThread[i] = 0;
        instancesPerThreads[i] = generalNumberOfInstances;
        if (i < rest)
            instancesPerThreads[i]++;

        threadResults[i].resize(instancesPerThreads[i]);

        benchmarkThreads . emplace_back( run_benchmark, i );
    }

    for(auto &thread: benchmarkThreads)
        thread.join();


    std::ofstream outputFile;
    outputFile.open(OUTPUT_FILE, std::ofstream::out | std::ofstream::trunc);

    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
        for (int j = 0; j < threadResults[i].size(); j++){
            outputFile << threadResults[i][j] << "\n";
        }
    }
    long double totalTime = 0;
    int nTimeouts = 0;
    for (int i = 0; i < NUMBER_OF_THREADS; i++)
    {
        nTimeouts += timeoutPerThread[ i ];
        totalTime += timePerThread[ i ];
    }


    std::string conclusion = std::to_string( (weighted_dataset?data_weighted.size():data_unweighted.size()) - nTimeouts - benchmarksNotFound) +
            " benchmarks have been successfully executed over a total time of "
            + std::to_string(totalTime) + " seconds. " + std::to_string(nTimeouts) + " benchmarks have failed due to a timeout.";

    std::cout << conclusion << std::endl;
    std::cout << "Check " << OUTPUT_FILE << " for results." << std::endl;
    outputFile << conclusion << std::endl;

    return 0;
}
