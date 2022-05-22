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

#include "unweighted_data.h"

// g++ EvalBenchmarking.cpp -o EvalBenchmarking -lpthread
// Warning : if you interrupt the process, the threads will keep going as I didn't handle that case

// !!! Modify the following args !!!
const std::string MAXSAT_BIN_PATH = "/home/carle/.ssh/CadicalEval/EvalMaxSAT_bin";
const std::string BENCHMARK_FILES_FOLDER = "/media/carle/UQAM/Recherche/2022_files/";
const std::string OUTPUT_FILE = "./output";
const std::string BENCHMARK_TIMEOUT = "3600"; // In seconds
const int NUMBER_OF_THREADS = 16;
// #################################


std::vector<int> instancesPerThreads;
std::vector<long double> timePerThread;
std::vector<int> timeoutPerThread;
std::vector<std::vector<std::string>> threadResults;
std::vector<std::thread> benchmarkThreads;
int benchmarksNotFound = 0; // Not thread-safe to use a simple int here but rarely used so wtv

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

// This function may be ugly and rigid but hey, at least it's safe
std::string parse_result(std::string result, int threadNumber) {
    std::stringstream stream(result);
    std::string temp;
    std::string output;

    stream >> temp;
    if (temp != "s") return "-1";

    stream . ignore( std::numeric_limits<std::streamsize>::max(), stream . widen( '\n' ));

    stream >> temp;
    if (temp != "o") return "-1";

    stream >> output; // Getting the cost

    stream >> temp;
    if (temp != "v")return "-1";

    stream >> temp;
    if (temp != "c") return "-1";

    stream >> temp;
    if (temp != "Total") return "-1";

    stream >> temp;
    if (temp != "time:") return "-1";

    stream >> temp; // Time
    long double time = std::stod(temp);
    stream >> temp; // Time unit
    if (temp == "ms")
        time /= 1000;
    if (temp == "µs")
        time /= 1000000;
    timePerThread[threadNumber] += time;
    output = std::to_string(time) + "s (" + output + ")";

    return output;
}

void run_benchmark( int threadNumber) {

    int startIndex = 0;
    for (int i = 0; i < threadNumber; i++)
        startIndex += instancesPerThreads[i];

    int resultIndex = 0;
    for (int i = startIndex; i < startIndex + instancesPerThreads[threadNumber] - 1; i++, resultIndex++) {
        std::string path = BENCHMARK_FILES_FOLDER + data_unweighted[i];

        if (!file_exists(path))
        {
            std::cerr << "The following file, at index " << i << ", does not exist : " << std::endl << path << std::endl;
            benchmarksNotFound++;
            continue;
        }
        std::string cmdString = "timeout " + BENCHMARK_TIMEOUT + " " + MAXSAT_BIN_PATH + " " + path + " 2> /dev/null";
        const char* cmdChar = cmdString.c_str();

        std::string result = exec(cmdChar);
        std::cout << path << std::endl;
        if (result == "c Interrupt signal (15) received.\n")
        {
            result = data_unweighted[ i ] + "\n" + BENCHMARK_TIMEOUT + "s (-)\n\n";
            timeoutPerThread[threadNumber]++;
        }
        else
        {
            std::string parsedResult = parse_result( result, threadNumber );
            if (parsedResult == "-1") {
                std::cerr << "Parsing error in " << path << " (caused by timeout). Skipping file." << std::endl;
                benchmarksNotFound++;
                continue;
            }
            result = data_unweighted[ i ] + "\n" + parsedResult + "\n\n";
        }
        threadResults[ threadNumber ][ resultIndex ] = result;
    }
}



int main()
{
    if (!file_exists(MAXSAT_BIN_PATH))
    {
        std::cerr << "Invalid path for the EvalMaxSAT binary." << std::endl;
        exit(-1);
    }

    if (!file_exists(BENCHMARK_FILES_FOLDER))
    {
        std::cerr << "Invalid path for the folder containing the benchmark files." << std::endl;
        exit(-1);
    }

    if (!file_exists(OUTPUT_FILE))
    {
        std::cerr << "Invalid path for the output file." << std::endl;
        exit(-1);
    }


    std::cout << "Starting benchmark. Result will be inserted into OUTPUT_FILE as defined above." << std::endl;
    sleep(3);

    instancesPerThreads.resize(NUMBER_OF_THREADS);
    threadResults.resize(NUMBER_OF_THREADS);
    timePerThread.resize( NUMBER_OF_THREADS);
    timeoutPerThread.resize(NUMBER_OF_THREADS);
    benchmarkThreads.reserve(NUMBER_OF_THREADS);

    int generalNumberOfInstances = data_unweighted.size() / NUMBER_OF_THREADS;
    int rest = data_unweighted.size() % NUMBER_OF_THREADS;
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
            outputFile << threadResults[i][j];
        }
    }
    long double totalTime = 0;
    int nTimeouts = 0;
    for (int i = 0; i < NUMBER_OF_THREADS; i++)
    {
        nTimeouts += timeoutPerThread[ i ];
        totalTime += timePerThread[ i ];
    }


    std::string conclusion = std::to_string( data_unweighted.size() - nTimeouts - benchmarksNotFound) +
            " benchmarks have been successfully executed over a total time of "
            + std::to_string(totalTime) + " seconds. " + std::to_string(nTimeouts) + " benchmarks have failed due to a timeout.";

    std::cout << conclusion << std::endl;
    std::cout << "Check " << OUTPUT_FILE << " for results." << std::endl;
    outputFile << conclusion << std::endl;

    return 0;
}
