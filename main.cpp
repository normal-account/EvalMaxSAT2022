#include <iostream>
#include <cassert>
#include <csignal>
#include <zlib.h>

#include "EvalMaxSAT.h"
#include "lib/CLI11.hpp"

// Pour les tests
#include "unweighted_data.h"
#include "weighted_data.h"




using namespace MaLib;

EvalMaxSAT* monMaxSat = nullptr;

void signalHandler( int signum ) {
    std::cout << "c Interrupt signal (" << signum << ") received." << std::endl;
    std::cout << "c o >=" << monMaxSat->getCost() << std::endl;
    std::cout << "s UNKNOWN" << std::endl;

   delete monMaxSat;

   exit(signum);
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

long calculateCost(const std::string & file, const std::vector<bool> &result) {
    long cost = 0;
    auto in_ = gzopen(file.c_str(), "rb");

                StreamBuffer in(in_);

                bool weighted = true;
                int64_t top = -1;
                int64_t weight = 1;

                std::vector<int> lits;
                int vars = 0;
                int inClauses = 0;
                int count = 0;
                for(;;) {
                    skipWhitespace(in);

                    if(*in == EOF)
                        break;

                    else if(*in == 'c')
                        skipLine(in);
                    else {
                        count++;
                        if(weighted)
                            weight = parseInt64(in);
                        readClause(in, lits);
                        if(weight == 0) {
                            bool sat=false;
                            for(auto l: lits) {
                                assert(abs(l) < result.size());
                                if ( (l>0) == (result[abs(l)]) ) {
                                    sat = true;
                                    break;
                                }
                            }
                            assert(sat);
                        } else {
                            bool sat=false;
                            for(auto l: lits) {
                                assert(abs(l) < result.size());

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


int main(int argc, char *argv[]) {

    for(unsigned int id = 0; id<data_unweighted.size(); id++) {
        srand(0);

        monMaxSat = new EvalMaxSAT();

        std::string filePath = "/media/carle/UQAM/Recherche/2022_files/" + data_unweighted[id]; // For a custom path
        //filePath = "/media/carle/UQAM/Recherche/2022_files/simp-cf_15.03.wcnf.gz"; data_unweighted_cost[id] = 18;
        MaLib::Chrono C( filePath);

        auto in = gzopen( filePath.c_str(), "rb");
        if(!monMaxSat->parse(in)) { // TODO : rendre robuste au header mismatch
            std::cerr << "Impossible de lire le fichier" << std::endl;
            assert(false);
            return -1;
        }

        gzclose(in);

        if(!monMaxSat->solve()) {
            std::cerr << "Pas de solution ?!?" << std::endl;
            assert(false);
            return -1;
        }

        if( monMaxSat->getCost() != data_unweighted_cost[id]) {
            std::cerr << "id = " << id << std::endl;
            std::cerr << "file = " << filePath << std::endl;
            std::cerr << "Résultat éroné : \n   Trouvé : " << monMaxSat->getCost() << "\n  Attendu : " << data_unweighted_cost[id] << std::endl;
            std::vector<bool> assign;
            assign.push_back(0); // fake var_0

            for(unsigned int i=1; i<=data_unweighted_nVars[id]; i++) {
                assign.push_back(monMaxSat->getValue(i));
            }

            std::cerr << " RealCost = " << calculateCost( filePath, assign) << std::endl;

            assert(false);
            return -1;
        } else {

            std::vector<bool> assign;
            assign.push_back(0); // fake var_0
            for(unsigned int i=1; i<=data_unweighted_nVars[id]; i++) {
                assign.push_back(monMaxSat->getValue(i));
            }

            if( calculateCost( filePath, assign) != monMaxSat->getCost() ) {
                std::cerr << "o Error: " << calculateCost( filePath, assign) << " != " << monMaxSat->getCost() << std::endl;
            }
            assert( calculateCost( filePath, assign) == monMaxSat->getCost() );
        }
        delete monMaxSat;
        //break;  // TODO: !!! REMOVE !!!
    }
}

int mainSAVE(int argc, char *argv[])
{
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

    CLI11_PARSE(app, argc, argv);
    ////////////////////////////////////////


    auto monMaxSat = new EvalMaxSAT(paralleleThread);
    monMaxSat->setTimeOutFast(timeOutFastMinimize);
    monMaxSat->setCoefMinimize(coefMinimizeTime);

    auto in = gzopen(file.c_str(), "rb");
    if(!monMaxSat->parse(in)) {
        return -1;
    }

    if(!monMaxSat->solve()) {
        std::cout << "s UNSATISFIABLE" << std::endl;
        return 0;
    }

    ////// PRINT SOLUTION //////////////////
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

    delete monMaxSat;
    return 0;
}



