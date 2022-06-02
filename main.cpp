#include <iostream>
#include <cassert>
#include <csignal>
#include <zlib.h>

#include "EvalMaxSAT.h"
#include "lib/CLI11.hpp"

// Pour les tests
#include "unweighted_data.h"
#include "weighted_data.h"

#include "config.h"

using namespace MaLib;

EvalMaxSAT* monMaxSat = nullptr;

void signalHandler( int signum ) {
    std::cout << "c Interrupt signal (" << signum << ") received." << std::endl;
    std::cout << "c o >=" << monMaxSat->getCost() << std::endl;
    std::cout << "s UNKNOWN" << std::endl;

   delete monMaxSat;

   exit(signum);
}



int test(bool weighted=false) {
    Chrono chrono("c Total time");

    std::cout << "Time (sec) \t File" << std::endl;
    for(unsigned int id = 0 ; id < (weighted?data_weighted.size():data_unweighted.size()); id++) {
        srand(0);
        std::cout << (weighted?data_weighted[id]:data_unweighted[id]) << "\t" << std::flush;

        monMaxSat = new EvalMaxSAT();

        std::string filePath = (weighted?BENCHMARK_FILES_FOLDER_WEIGHTED:BENCHMARK_FILES_FOLDER_UNWEIGHTED) + (weighted?data_weighted[id]:data_unweighted[id]); // For a custom path

        MaLib::Chrono C;


        if(!monMaxSat->parse(filePath)) { // TODO : rendre robuste au header mismatch
            std::cerr << "Impossible de lire le fichier : " << filePath << std::endl;
            assert(false);
            return -1;
        }

        if(!monMaxSat->solve()) {
            std::cerr << "Pas de solution ?!?" << std::endl;
            assert(false);
            return -1;
        }

        if( monMaxSat->getCost() != (weighted?data_weighted_cost[id]:data_unweighted_cost[id])) {
            std::cerr << "id = " << id << std::endl;
            std::cerr << "file = " << filePath << std::endl;
            std::cerr << "Résultat éroné : \n   Trouvé : " << monMaxSat->getCost() << "\n  Attendu : " << (weighted?data_weighted_cost[id]:data_unweighted_cost[id]) << std::endl;
            std::vector<bool> assign;
            assign.push_back(0); // fake var_0

            for(unsigned int i=1; i<=monMaxSat->nInputVars; i++) {
                assign.push_back(monMaxSat->getValue(i));
            }

            std::cerr << " RealCost = " << calculateCost( filePath, assign) << std::endl;

            assert(false);
            return -1;
        } else {

            std::vector<bool> assign;
            assign.push_back(0); // fake var_0
            for(unsigned int i=1; i<=monMaxSat->nInputVars; i++) {
                assign.push_back(monMaxSat->getValue(i));
            }

            if( calculateCost( filePath, assign) != monMaxSat->getCost() ) {
                std::cerr << "o Error: " << calculateCost( filePath, assign) << " != " << monMaxSat->getCost() << std::endl;
            }
//            assert( calculateCost( filePath, assign) == monMaxSat->getCost() );
        }
        std::cout << C.tacSec() << std::endl;
        delete monMaxSat;
    }
    return 0;
}

int main(int argc, char *argv[])
{
    if(argc==1) {
        // TODO : cette section est juste pour le dévelopement
        bool TESTER_LE_CAS_WEIGHTED = true;
        return test( TESTER_LE_CAS_WEIGHTED );
    }

    Chrono chrono("c Total time");
    signal(SIGINT, signalHandler);
    signal(SIGTERM, signalHandler);

    /////// PARSE ARG //////////////////////
    CLI::App app{"EvalMaxSAT Solver"};

    std::string file;
    app.add_option("file", file, "File with the formula to be solved (wcnf format)")->check(CLI::ExistingFile)->required();

    unsigned int paralleleThread=0;
    app.add_option("-p", paralleleThread, toString("Number of minimization threads (default = ",paralleleThread,")"));

    unsigned int timeOutFastMinimize=60;
    app.add_option("--timeout_fast", timeOutFastMinimize, toString("Timeout in second for fast minimize (default = ",timeOutFastMinimize,")"));

    unsigned int coefMinimizeTime=2;
    app.add_option("--coef_minimize", coefMinimizeTime, toString("Multiplying coefficient of the time spent to minimize cores (default = ",coefMinimizeTime,")"));

    bool oldOutputFormat = false;
    app.add_flag("--old", oldOutputFormat, "Use old output format.");

    bool bench = false;
    app.add_flag("--bench", bench, "Print result in one line");

    CLI11_PARSE(app, argc, argv);
    ////////////////////////////////////////


    auto monMaxSat = new EvalMaxSAT(paralleleThread);
    monMaxSat->setTimeOutFast(timeOutFastMinimize);
    monMaxSat->setCoefMinimize(coefMinimizeTime);

    if(!monMaxSat->parse(file)) {
        return -1;
    }

    if(!monMaxSat->solve()) {
        std::cout << "s UNSATISFIABLE" << std::endl;
        return 0;
    }


    if(bench) {
        std::cout << file << "\t" << monMaxSat->getCost() << "\t" << chrono.tacSec() << std::endl;
        chrono.afficherQuandDetruit(false);
        C_solve.afficherQuandDetruit(false);
        C_fastMinimize.afficherQuandDetruit(false);
        C_fullMinimize.afficherQuandDetruit(false);
        C_extractAM.afficherQuandDetruit(false);
        C_harden.afficherQuandDetruit(false);
        C_extractAMAfterHarden.afficherQuandDetruit(false);
    } else if(oldOutputFormat) {
        ////// PRINT SOLUTION OLD FORMAT //////////////////
        std::cout << "s OPTIMUM FOUND" << std::endl;
        std::cout << "o " << monMaxSat->getCost() << std::endl;
        std::cout << "v";
        for(unsigned int i=1; i<=monMaxSat->nInputVars; i++) {
            if(monMaxSat->getValue(i))
                std::cout << " " << i;
            else
                std::cout << " -" << i;
        }
        std::cout << std::endl;
        ///////////////////////////////////////
    } else {
        ////// PRINT SOLUTION NEW FORMAT //////////////////
        std::cout << "s OPTIMUM FOUND" << std::endl;
        std::cout << "o " << monMaxSat->getCost() << std::endl;
        std::cout << "v ";
        for(unsigned int i=1; i<=monMaxSat->nInputVars; i++) {
            std::cout << monMaxSat->getValue(i);
        }
        std::cout << std::endl;
        ///////////////////////////////////////
    }


    delete monMaxSat;
    return 0;
}



