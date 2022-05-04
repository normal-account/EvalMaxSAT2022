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
        parsed_lit = Glucose::parseInt(in);
        if (parsed_lit == 0) break;
        lits.push_back( parsed_lit );
    }
}



long calculateCost(const std::string & file, const std::vector<bool> &result) {
    long cost = 0;
    auto in_ = gzopen(file.c_str(), "rb");


                Glucose::StreamBuffer in(in_);

                bool weighted = false;
                int64_t top = -1;
                int64_t weight = 1;

                std::vector<int> lits;
                int vars = 0;
                int inClauses = 0;
                int count = 0;
                for(;;) {
                    Glucose::skipWhitespace(in);

                    if(*in == EOF)
                        break;

                    if(*in == 'p') {
                        ++in;
                        if(*in != ' ') {
                            std::cerr << "o PARSE ERROR! Unexpected char: " << static_cast<char>(*in) << std::endl;
                            return false;
                        }
                        ++in;
                        if(*in == 'w') { weighted = true; ++in; }

                        if(Glucose::eagerMatch(in, "cnf")) {
                            vars = Glucose::parseInt(in);
                            /*setNInputVars(vars);
                            for(int i=0; i<vars; i++) {
                                newVar();
                            }*/
                            inClauses = Glucose::parseInt(in);
                            if(weighted && *in != '\n')
                                top = Glucose::parseInt64(in);
                        } else {
                            std::cerr << "o PARSE ERROR! Unexpected char: " << static_cast<char>(*in) << std::endl;
                            return false;
                        }
                    }
                    else if(*in == 'c')
                        Glucose::skipLine(in);
                    else {
                        count++;
                        if(weighted)
                            weight = Glucose::parseInt64(in);
                        readClause(in, lits);
                        if(weight >= top) {
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
                if(count != inClauses) {
                    std::cerr << "o WARNING! DIMACS header mismatch: wrong number of clauses." << std::endl;
                    //return false;
                }


    gzclose(in_);
    return cost;
}



int main(int argc, char *argv[]) {

    for(unsigned int id = 0; id<data_weighted.size(); id++) {
        srand(0);

        MaLib::Chrono C(data_weighted[id]);

        monMaxSat = new EvalMaxSAT();


        auto in = gzopen(data_weighted[id].c_str(), "rb");
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

        if( monMaxSat->getCost() != data_weighted_cost[id]) {
            std::cerr << "id = " << id << std::endl;
            std::cerr << "file = " << data_weighted[id] << std::endl;
            std::cerr << "Résultat éroné : \n   Trouvé : " << monMaxSat->getCost() << "\n  Attendu : " << data_weighted[id] << std::endl;

            std::vector<bool> assign;
            assign.push_back(0); // fake var_0
            for(unsigned int i=1; i<=monMaxSat->nInputVars; i++) {
                assign.push_back(monMaxSat->getValue(i));
            }
            std::cerr << " RealCost = " << calculateCost(data_weighted[id], assign) << std::endl;


            assert(false);
            return -1;
        } else {

            std::vector<bool> assign;
            assign.push_back(0); // fake var_0
            for(unsigned int i=1; i<=monMaxSat->nInputVars; i++) {
                assign.push_back(monMaxSat->getValue(i));
            }

            if( calculateCost(data_weighted[id], assign) != monMaxSat->getCost() ) {
                std::cerr << "o Error: " << calculateCost(data_weighted[id], assign) << " != " << monMaxSat->getCost() << std::endl;
            }
            assert( calculateCost(data_weighted[id], assign) == monMaxSat->getCost() );
        }


        delete monMaxSat;
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



