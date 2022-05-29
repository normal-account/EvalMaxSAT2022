#ifndef EVALMAXSAT_SLK178903R_H
#define EVALMAXSAT_SLK178903R_H

#include <iostream>
#include <vector>
#include <algorithm>
#include <random>

#include "communicationlist.h"
#include "Chrono.h"
#include "coutUtil.h"
#include "virtualmaxsat.h"
#include "virtualsat.h"
#include "cadicalinterface.h"
#include "mcqd.h"
#include "coutUtil.h"

using namespace MaLib;

MaLib::Chrono C_solve("Cumulative time spent solving SAT formulas");
MaLib::Chrono C_fastMinimize("Cumulative time spent for fastMinimize");
MaLib::Chrono C_fullMinimize("Cumulative time spent for fullMinimize");
MaLib::Chrono C_extractAM("Cumulative time spent for extractAM");


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


t_weight calculateCost(const std::string & file, const std::vector<bool> &result) {
    long cost = 0;
    auto in_ = gzopen(file.c_str(), "rb");
    t_weight weightForHardClause = -1;

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
                        count++;
                        weight = parseWeight(in);
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


class EvalMaxSAT : public VirtualMAXSAT {
    unsigned int nbMinimizeThread;

    VirtualSAT *solver = nullptr;
    std::vector<VirtualSAT*> solverForMinimize;

    //int nVars = 0;
    int nVarsInSolver;

    std::vector<t_weight> _weight; // Weight of var at index, 0 if hard
    std::vector<bool> model; // Sign of var at index
    std::vector<int> mapAssum2card; // Soft var as index to get the index of CardIncremental_Lazy object in save_card
    std::vector< std::tuple<std::shared_ptr<VirtualCard>, int, t_weight> > save_card; // Contains CardIncremental_Lazy objects, aka card. constraints

    std::map<t_weight, std::set<int>> mapWeight2Assum; // Used for the weighted case

    MaLib::Chrono chronoLastSolve;

    std::atomic<t_weight> cost = 0;
    unsigned int _timeOutFastMinimize=60; // TODO: Magic number
    unsigned int _coefMinimizeTime = 2.0; // TODO: Magic number

    ///// For communication between threads
    MaLib::CommunicationList< std::tuple<std::list<int>, long> > CL_ConflictToMinimize;
    MaLib::CommunicationList< int > CL_LitToUnrelax; // Variables to remove from the assumptions and put back in core
    MaLib::CommunicationList< int > CL_LitToRelax; // Variables to try to relax the cardinality constraint with which they're related
    MaLib::CommunicationList< std::tuple<std::vector<int>, bool, t_weight> > CL_CardToAdd; // Cores for which to add cardinality constraints
    std::atomic<unsigned int> numberMinimizeThreadRunning;
    /////



    struct CompLit {
      bool operator() (const int& a, const int& b) const {
          if(abs(a) < abs(b))
              return true;

          if(abs(a) == abs(b))
              return (a>0) && (b<0);

          return false;
      }
    };

    std::set<int> _assumption;


    t_weight removeSameAmount(std::vector<int>& lits) {
        t_weight result = _weight[ abs(lits[0]) ];
        for(auto l: lits) {
            if(result > _weight[ abs(l) ]) {
                result = _weight[ abs(l) ];
            }
        }
        for(unsigned int i=0; i<lits.size(); ) {
            assert( mapWeight2Assum[abs(lits[i])].count(lits[i]) );
            mapWeight2Assum[abs(lits[i])].erase(lits[i]);
            _weight[ abs(lits[i]) ] -= result;

            if(_weight[ abs(lits[i]) ] == 0) {
                _assumption.erase(lits[i]);
                lits[i] = lits.back();
                lits.pop_back();
                if(mapAssum2card[abs(lits[i])]) {
                    CL_LitToRelax.push(lits[i]);
                }
            } else {
                mapWeight2Assum[abs(lits[i])].insert(lits[i]);
                i++;
            }
        }
        return result;
    }

    //////////////////////////////
    ////// For extractAM ////////
    ////////////////////////////
    void extractAM() {
        adapt_am1_exact();
        adapt_am1_FastHeuristicV7();
    }

   void reduceCliqueV2(std::list<int> & clique) {
       for(auto posImpliquant = clique.begin() ; posImpliquant != clique.end() ; ++posImpliquant) {
           auto posImpliquant2 = posImpliquant;
           for(++posImpliquant2 ; posImpliquant2 != clique.end() ; ) {
               if(solver->solveLimited(std::vector<int>({-(*posImpliquant), -(*posImpliquant2)}), 10000) != -1) {
                   posImpliquant2 = clique.erase(posImpliquant2);
               } else {
                   ++posImpliquant2;
               }
           }
       }
   }

   bool adapt_am1_FastHeuristicV7() {
       MonPrint("adapt_am1_FastHeuristic");
       Chrono chrono;
       std::vector<int> prop;
       unsigned int nbCliqueFound=0;

       // TODO : trier les var en fonction du nombre de fois où elles apparaissent dans la formule

       // Where nVarsInSolver represents the number of vars before the cardinality constraints. We don't want to
       // propagate soft vars representing cardinality constraints.     // TODO: pour quoi pas ?
       for(unsigned int VAR = 1; VAR<nVarsInSolver; VAR++) {
           if(_weight[VAR] == 0)
               continue;

           assert(_weight[VAR] > 0);
           int LIT = model[VAR]?static_cast<int>(VAR):-static_cast<int>(VAR);
           prop.clear();
           if(solver->propagate({LIT}, prop)) {
               if(prop.size() == 0)
                   continue;
               if(prop.size() == 1)
                   continue;

               std::list<int> clique;
               for(auto litProp: prop) {
                   if(isInAssum(-litProp)) {
                       clique.push_back(litProp);
                       assert(solver->solve(std::vector<int>({-litProp, LIT})) == false);
                   }
               }

               if(clique.size() == 0)
                   continue;

               reduceCliqueV2(clique); // retirer des elements pour que clique soit une clique

               clique.push_back(-LIT);

               if(clique.size() >= 2) {
                   nbCliqueFound++;

                   std::vector<int> clause;
                   for(auto lit: clique)
                       clause.push_back(-lit);

                   processAtMostOne(clause);
               }
           } else {
               addClause({-LIT});
           }
       }

       MonPrint(nbCliqueFound, " cliques found in ", chrono.tac() / 1000, "ms.");
       return true;
   }

   bool adapt_am1_exact() {
       Chrono chrono;
       unsigned int nbCliqueFound=0;
       std::vector<int> assumption;

       for(unsigned int i=1; i<_weight.size(); i++) {
           if(_weight[i] > 0) {
               if(model[i]) {
                   assumption.push_back(static_cast<int>(i));
               } else {
                   assumption.push_back(-static_cast<int>(i));
               }
           }
       }

       // TODO : dans le cas weighted, stratifier ?

       MonPrint("Nombre d'assumption: ", assumption.size());

       if(assumption.size() > 30000) { // hyper paramétre
           MonPrint("skip");
           return false;
       }

       MonPrint("Create graph for searching clique...");
       unsigned int size = assumption.size();
       bool **conn = new bool*[size];
       for(unsigned int i=0; i<size; i++) {
           conn[i] = new bool[size];
           for(unsigned int x=0; x<size; x++)
               conn[i][x] = false;
       }

       MonPrint("Create link in graph...");
       for(unsigned int i=0; i<size; ) {
           int lit1 = assumption[i];


           std::vector<int> prop;
           // If literal in assumptions has a value that is resolvable, get array of all the other literals that must have
           // a certain value in consequence, then link said literal to the opposite value of these other literals in graph

           if(solver->propagate({lit1}, prop)) {
               for(int lit2: prop) {
                   for(unsigned int j=0; j<size; j++) {
                       if(j==i)
                           continue;
                       if(assumption[j] == -lit2) {
                           conn[i][j] = true;
                           conn[j][i] = true;
                       }
                   }
               }
               i++;
           } else { // No solution - Remove literal from the assumptions and add its opposite as a clause
               addClause({-lit1});

               assumption[i] = assumption.back();
               assumption.pop_back();

               for(unsigned int x=0; x<size; x++) {
                   conn[i][x] = false;
                   conn[x][i] = false;
               }

               size--;
           }
       }


       if(size == 0) {
           for(unsigned int i=0; i<size; i++) {
               delete conn[i];
           }
           delete [] conn;
           return true;
       }

       std::vector<bool> active(size, true);
       for(;;) {
           int *qmax;
           int qsize=0;
           Maxclique md(conn, size, 0.025);
           md.mcqdyn(qmax, qsize, 100000);

           if(qsize <= 2) { // Hyperparametre: Taille minimal a laquelle arreter la methode exact
               for(unsigned int i=0; i<size; i++) {
                   delete conn[i];
               }
               delete [] conn;
               delete qmax;

               MonPrint(nbCliqueFound, " cliques found in ", (chrono.tac() / 1000), "ms.");
               return true;
           }
           nbCliqueFound++;

           {
               //int newI=qmax[0];
               std::vector<int> clause;

               for (unsigned int i = 0; i < qsize; i++) {
                   int lit = assumption[qmax[i]];
                   active[qmax[i]] = false;
                   clause.push_back(lit);

                   for(unsigned int x=0; x<size; x++) {
                       conn[qmax[i]][x] = false;
                       conn[x][qmax[i]] = false;
                   }
               }
               auto newAssum = processAtMostOne(clause);
               assert(qsize >= newAssum.size());

               for(unsigned int j=0; j<newAssum.size() ; j++) {
                   assumption[ qmax[j] ] = newAssum[j];
                   active[ qmax[j] ] = true;

                   std::vector<int> prop;
                   if(solver->propagate({newAssum[j]}, prop)) {
                       for(int lit2: prop) {
                           for(unsigned int k=0; k<size; k++) {
                               if(active[k]) {
                                   if(assumption[k] == -lit2) {
                                       conn[qmax[j]][k] = true;
                                       conn[k][qmax[j]] = true;
                                   }
                               }
                           }
                       }
                    } else {
                       assert(solver->solve(std::vector<int>({newAssum[j]})) == false);
                       addClause({-newAssum[j]});
                    }
               }
           }

           delete qmax;
       }

       assert(false);
   }

   // Harden soft vars in passed clique to then unrelax them via a new cardinality constraint
   std::vector<int> processAtMostOne(std::vector<int> clause) {
       // Works also in the weighted case
       std::vector<int> newAssum;

       while(clause.size() > 1) {
           auto saveClause = clause;
           t_weight w = _weight[ abs(clause[0]) ];

           for(unsigned int i=1; i<clause.size(); i++) {
               if( w > _weight[ abs(clause[i]) ] ) {
                   w = _weight[ abs(clause[i]) ];
               }
           }
           assert(w > 0);

           for(unsigned int i=0; i<clause.size(); ) {
               assert( model[ abs(clause[i]) ] == (clause[i]>0) );

               assert( mapWeight2Assum[ _weight[ abs(clause[i]) ] ].count( clause[i] ) );
               mapWeight2Assum[ _weight[ abs(clause[i]) ] ].erase( clause[i] );
               _weight[ abs(clause[i]) ] -= w;

               if( _weight[ abs(clause[i]) ] == 0 ) {
                   //removeLitFromAssum(clause[i]);
                   _assumption.erase( clause[i] );
                   clause[i] = clause.back();
                   clause.pop_back();
               } else {
                   mapWeight2Assum[ _weight[ abs(clause[i]) ] ].insert( clause[i] );
                   i++;
               }
           }
           MonPrint("AM1: cost = ", cost, " + ", w * (t_weight)(saveClause.size()-1));
           cost += w * (t_weight)(saveClause.size()-1);

           assert(saveClause.size() > 1);
           newAssum.push_back( addWeightedClause(saveClause, w) );
           assert( _weight[ abs(newAssum.back()) ] > 0 );
           assert( model[ abs(newAssum.back()) ]  == (newAssum.back() > 0) );
       }

       if( clause.size() ) {
           newAssum.push_back(clause[0]);
       }
       return newAssum;
   }





public:
    EvalMaxSAT(unsigned int nbMinimizeThread=0, VirtualSAT *solver =
            new CadicalInterface()
    ) : nbMinimizeThread(nbMinimizeThread), solver(solver)
    {
        for(unsigned int i=0; i<nbMinimizeThread; i++) {
            solverForMinimize.push_back(new CadicalInterface());
        }

        _weight.push_back(0);           //
        model.push_back(false);         // Fake lit with id=0
        mapAssum2card.push_back(-1);    //


        C_solve.tic();
        C_solve.pause(true);
        C_fastMinimize.tic();
        C_fastMinimize.pause(true);
        C_fullMinimize.tic();
        C_fullMinimize.pause(true);
        C_extractAM.tic();
        C_extractAM.pause(true);
    }

    virtual ~EvalMaxSAT();

   void addClause( const std::vector<int> &clause) override {
       if(clause.size() == 1) {
           if(_weight[abs(clause[0])] != 0) {

               if( (clause[0]>0) == model[abs(clause[0])] ) {
                   assert( mapWeight2Assum[ _weight[abs(clause[0])] ].count( clause[0] ) );
                   mapWeight2Assum[ _weight[abs(clause[0])] ].erase( clause[0] );
                   _weight[abs(clause[0])] = 0;
                   _assumption.erase(clause[0]);
               } else {
                   assert( mapWeight2Assum[ _weight[abs(clause[0])] ].count( -clause[0] ) );
                   mapWeight2Assum[ _weight[abs(clause[0])] ].erase( -clause[0] );
                   cost += _weight[abs(clause[0])];
                   _weight[abs(clause[0])] = 0;
                   _assumption.erase(-clause[0]);
               }

               return;
           }
       }

       solver->addClause( clause );
       for(auto s : solverForMinimize) {
           s->addClause( clause );
       }
   }

    virtual void simplify() {
        assert(!"TODO");
    }

    virtual unsigned int nVars() override {
        return solver->nVars();
    }

    virtual bool solve(const std::vector<int> &assumption) {
        assert(!"TODO");
    }

    virtual int solveLimited(const std::vector<int> &assumption, int confBudget) {
        assert(!"TODO");
    }

    virtual std::vector<int> getConflict() {
        assert(!"TODO");
    }


    bool isInAssum(int lit) {
        unsigned int var = static_cast<unsigned int>(abs(lit));
        if( _weight[var] > 0 ) {
            if( model[var] == (lit>0) )
                return true;
        }
        return false;
    }

    private:

    void minimize(VirtualSAT* S, std::list<int> & conflict, long refTime, bool doFastMinimize) {
        auto saveconflict = conflict;
/*        std::cout << "minimize initial" << std::endl;
        for(auto lit: conflict) {
            std::cout << "_weight["<<abs(lit)<<"] = " << _weight[abs(lit)] << std::endl;
            assert(_weight[abs(lit)] > 0);
        }
        std::cout << "---" << std::endl;
*/
        std::vector<int> uselessLit;
        std::vector<int> L;
        bool completed=false;
        t_weight minWeight = std::numeric_limits<t_weight>::max();
        if(!doFastMinimize) {
            std::set<int> conflictMin(conflict.begin(), conflict.end());
            completed = fullMinimize(S, conflictMin, uselessLit, _coefMinimizeTime*refTime);
            for(auto lit: conflictMin) {
                L.push_back(-lit);
//                std::cout << "_weight["<<abs(lit)<<"] = " << _weight[abs(lit)] << std::endl;
                if(minWeight > _weight[abs(lit)]) {
                    minWeight = _weight[abs(lit)];
                }
            }

            assert(minWeight > 0);
            for(auto lit: conflictMin) {
                assert( mapWeight2Assum[ _weight[abs(lit)] ].count( lit ));
                mapWeight2Assum[ _weight[abs(lit)] ].erase( lit );
                _weight[abs(lit)] -= minWeight;
                if( _weight[abs(lit)] != 0) {
                    uselessLit.push_back( lit );
                    mapWeight2Assum[ _weight[abs(lit)] ].insert( lit );
                } else {
                    CL_LitToRelax.push(lit);
                }
            }

        } else {
            MonPrint("minimize: skip car plus de 100000 ");

            for(auto lit: conflict) {
                L.push_back(-lit);
                if(minWeight > _weight[abs(lit)]) {
                    minWeight = _weight[abs(lit)];
                }
            }
            assert(minWeight > 0);
            for(auto lit: conflict) {
                assert(mapWeight2Assum[ _weight[abs(lit)] ].count( lit ));
                mapWeight2Assum[ _weight[abs(lit)] ].erase( lit );
                _weight[abs(lit)] -= minWeight;
                if( _weight[abs(lit)] != 0) {
                    uselessLit.push_back( lit );
                    mapWeight2Assum[ _weight[abs(lit)] ].insert( lit );
                } else {
                    CL_LitToRelax.push(lit);
                }
            }
        }

        MonPrint("\t\t\tMain Thread: cost = ", cost, " + ", minWeight);
        cost += minWeight;

        CL_LitToUnrelax.pushAll(uselessLit);
/*
        std::cout << "useless:" << std::endl;
        for(auto lit: uselessLit) {
            std::cout << "_weight["<<abs(lit)<<"] = " << _weight[abs(lit)] << std::endl;
        }
        std::cout << "----" << std::endl;
*/
        if(L.size() > 1) {
            CL_CardToAdd.push({L, !completed, minWeight});
        }

        MonPrint("size conflict after Minimize: ", conflict.size());
    }

    void threadMinimize(unsigned int num, bool fastMinimize) {
        for(;;) {
            auto element = CL_ConflictToMinimize.pop();
            MonPrint("threadMinimize[",num,"]: Run...");

            if(!element) {
                break;
            }

            minimize(solverForMinimize[num], std::get<0>(*element), std::get<1>(*element), fastMinimize);
        }
    }

    void apply_CL_CardToAdd() {
        while(CL_CardToAdd.size()) {
            // Each "set" in CL_CardToAdd contains the literals of a core
            auto element = CL_CardToAdd.pop();
            assert(element);

            std::shared_ptr<VirtualCard> card = std::make_shared<CardIncremental_Lazy>(this, std::get<0>(*element), 1);
            //std::shared_ptr<VirtualCard> card = std::make_shared<Card_Lazy_OE>(this, std::get<0>(*element));


            // save_card contains our cardinality constraints
            save_card.push_back( {card, 1, std::get<2>(*element)} );

            int k = 1;

            int newAssumForCard = card->atMost(k); // Gets the soft variable corresponding to the cardinality constraint with RHS = 1

            assert(newAssumForCard != 0);

            // TODO: Exhaust semble n'avoir pas d'impacte sur les performences ?
            /*
            MonPrint("solveLimited for Exhaust...");
            if(std::get<1>(*element)) { // if clause hasn't been fully minimized
                // Relax (inc) while the cardinality constraint cannot be satisfied with no other assumptions ; aka exhaust
                while(solver->solveLimited(std::vector<int>({newAssumForCard}), 10000) == -1) {
                    k++;
                    std::cout << "Exhaust !!!!!" << std::endl;
                    MonPrint("cost = ", cost, " + ", std::get<2>(*element));
                    cost += std::get<2>(*element);
                    newAssumForCard = card->atMost(k);

                    if(newAssumForCard==0) {
                        break;
                    }
                }
                std::get<1>(save_card.back()) = k; // Update the rhs of the cardinality in the vector with its new value


            }
            MonPrint("Exhaust fini!");
            */

            if(newAssumForCard != 0) {
                assert( _weight[abs(newAssumForCard)] == 0 );
                _weight[abs(newAssumForCard)] = std::get<2>(*element);
                mapWeight2Assum[ _weight[abs(newAssumForCard)] ].insert( newAssumForCard );
                _assumption.insert( newAssumForCard );
                // Put cardinality constraint in mapAssum2card associated to softVar as index in mapAssum2card
                mapAssum2card[ abs(newAssumForCard) ] = save_card.size()-1;
            }
        }
    }

    void apply_CL_LitToRelax() {
        while(CL_LitToRelax.size()) {
            int lit = CL_LitToRelax.pop().value_or(0);
            assert(lit != 0);
            unsigned int var = abs(lit);

            assert( _weight[var] == 0 );
            _weight[var] = 0;

            if(mapAssum2card[var] != -1) { // If there is a cardinality constraint associated to this soft var
                int idCard = mapAssum2card[var]; // Get index in save_card
                assert(idCard >= 0);

                // Note : No need to increment the cost here, as this cardinality constraint will be added inside another
                // cardinality constraint, and its non-satisfiability within it would implicate a cost increment anyway...

                std::get<1>(save_card[idCard])++; // Increase RHS

                // Get soft var associated with cardinality constraint with increased RHS
                int forCard = (std::get<0>(save_card[idCard])->atMost(std::get<1>(save_card[idCard])));

                if(forCard != 0) {
                    _assumption.insert( forCard );
                    assert( _weight[abs(forCard)] == 0 );
                    _weight[abs(forCard)] = std::get<2>(save_card[idCard]);
                    mapWeight2Assum[_weight[abs(forCard)]].insert( forCard );
                    mapAssum2card[ abs(forCard) ] = idCard;
                }
            }
        }
    }


public:

    bool solve() override {



        // Reinit CL
        CL_ConflictToMinimize.clear();
        CL_LitToUnrelax.clear();
        CL_LitToRelax.clear();
        CL_CardToAdd.clear();

        nVarsInSolver = nVars(); // Freeze nVarsInSolver in time

        MonPrint("\t\t\tMain Thread: extractAM...");
        C_extractAM.pause(false);
        extractAM();
        C_extractAM.pause(true);


        _assumption.clear();    // TODO : garder _assumption a jour pour ne pas avoir a réinitialiser en debut de solve()
        for(unsigned int i=1; i<_weight.size(); i++) {
            if(_weight[i] > 0) {
                if(model[i]) {
                    _assumption.insert(static_cast<int>(i));
                } else {
                    _assumption.insert(-static_cast<int>(i));
                }
            }
        }

        std::vector<std::thread> vMinimizeThread;
        vMinimizeThread.reserve(nbMinimizeThread);
        for(unsigned int i=0; i<nbMinimizeThread; i++) {
            vMinimizeThread.emplace_back(&EvalMaxSAT::threadMinimize, this, i, _assumption.size() > 100000);
        }

         for(;;) {
            assert(CL_ConflictToMinimize.size()==0);
            assert(CL_LitToUnrelax.size()==0);
            assert(CL_LitToRelax.size()==0);
            assert(CL_CardToAdd.size()==0);
            numberMinimizeThreadRunning = nbMinimizeThread;

            bool firstSolve = true;
            for(;;) {
                chronoLastSolve.tic();
                MonPrint("\t\t\tMain Thread: Solve...");

                bool conflictFound;

                C_solve.pause(false);
                if(firstSolve) {
                    MonPrint("solve(",_assumption.size(),")...");
                    conflictFound = (solver->solve(_assumption) == false);
                } else {
                    MonPrint("solveLimited(",_assumption.size(),")...");
                    conflictFound = (solver->solveLimited(_assumption, 10000) == -1);
                }
                C_solve.pause(true);

                if(!conflictFound) {
                    MonPrint("\t\t\tMain Thread: Solve() is not false!");

                    if(firstSolve) {
                        CL_ConflictToMinimize.close(); // Va impliquer la fin des threads minimize
                        for(auto &t: vMinimizeThread)
                            t.join();

                        return true;
                    }

                    chronoLastSolve.pause(true);
                    MonPrint("\t\t\tMain Thread: CL_ConflictToMinimize.wait(nbMinimizeThread=",nbMinimizeThread,", true)...");
                    do {
                        // If variables are still being unrelaxed, then break as the cost may still be reduced
                        if(CL_LitToUnrelax.size()) {
                            MonPrint("\t\t\tMain Thread: CL_LitToUnrelax.size() = ", CL_LitToUnrelax.size());
                            break;
                        }
                        numberMinimizeThreadRunning = nbMinimizeThread - CL_ConflictToMinimize.getNumberWaiting();
                        assert(numberMinimizeThreadRunning <= nbMinimizeThread);

                        // Wait() returns the current amount of waiting threads with the task of minimizing - to revisit
                    } while( CL_ConflictToMinimize.wait(nbMinimizeThread, true) < nbMinimizeThread );
                    MonPrint("\t\t\tMain Thread: Fin boucle d'attente");

                    // If no variables are left to be unrelaxed, we're done
                    if(CL_LitToUnrelax.size()==0) {
                        MonPrint("\t\t\tMain Thread: CL_LitToUnrelax.size()==0");

                        MonPrint("\t\t\tMain Thread: CL_LitToRelax.size() = ", CL_LitToRelax.size());
                        apply_CL_LitToRelax();

                        MonPrint("\t\t\tMain Thread: CL_CardToAdd.size() = ", CL_CardToAdd.size());
                        apply_CL_CardToAdd();


                        break;
                    }

                    if(isWeighted()) {
                        if(harden()) {                      // TODO: analyser l'impacte de cette optimisation
                            adapt_am1_FastHeuristicV7();    // TODO: analyser l'impacte de cette optimisation
                        }
                    }

                    MonPrint("\t\t\tMain Thread: CL_LitToUnrelax.size()!=0");
                } else { // Conflict found
                    MonPrint("\t\t\tMain Thread: Solve = false");
                    chronoLastSolve.pause(true);

                    std::vector<int> bestUnminimizedConflict = solver->getConflict(_assumption);
                    //assert(solver->solve(bestUnminimizedConflict) == false);

                    // Special case in which the core is empty, meaning no solution can be found
                    if(bestUnminimizedConflict.empty()) {
                        cost = -1;
                        return false;
                    }

                    if(bestUnminimizedConflict.size() == 1) {
                        MonPrint("\t\t\tMain Thread: conflict size = 1");
                        MonPrint("\t\t\tMain Thread: cost = ", cost, " + ",  _weight[ abs(bestUnminimizedConflict[0]) ]);
                        cost += _weight[ abs(bestUnminimizedConflict[0]) ];

                        assert( mapWeight2Assum[_weight[abs(bestUnminimizedConflict[0])]].count( bestUnminimizedConflict[0] ) );
                        mapWeight2Assum[_weight[abs(bestUnminimizedConflict[0])]].erase( bestUnminimizedConflict[0] );
                        _weight[ abs(bestUnminimizedConflict[0]) ] = 0;
                        assert(_assumption.count(bestUnminimizedConflict[0]));
                        _assumption.erase(bestUnminimizedConflict[0]);
                        continue;
                    }


                    //MaLib::Chrono chronoForBreak;

                    std::list<int> conflictMin;
                    for(auto lit: bestUnminimizedConflict)
                        conflictMin.push_back(lit);

                    bool doFullMinimize = true;
                    if((_assumption.size() < 100000) && (conflictMin.size() > 1)) {
                        MonPrint("\t\t\tMain Thread: fastMinimize(", conflictMin.size(), ")");
                        // If the fastMinimize is timed out, don't execute the full one as it would be too long
                        doFullMinimize = fastMinimize(solver, conflictMin);
                    }

                    MonPrint("\t\t\tMain Thread: taille final du conflict = ", conflictMin.size());

                    if(conflictMin.size() == 1) {
                        MonPrint("\t\t\tMain Thread: Optimal found, no need to fullMinimize");
                        doFullMinimize = false;
                    }

                    if(doFullMinimize) {
                        MonPrint("\t\t\tMain Thread: call CL_ConflictToMinimize.push");

                        // Remove problematic literals from the assumptions
                        for(auto lit: conflictMin) {
                            assert(_assumption.count(lit));
                            _assumption.erase(lit);
                        }
                        if(nbMinimizeThread == 0) {
                            minimize(solver, conflictMin, chronoLastSolve.tac(), _assumption.size() > 100000);
                        } else {
                            CL_ConflictToMinimize.push({conflictMin, chronoLastSolve.tac()});
                        }

                        firstSolve = false;
                    } else {

                        t_weight minWeight = _weight[abs(*(conflictMin.begin()))];
                        MonPrint("\t\t\tMain Thread: new card");
                        std::vector<int> L;
                        for(auto lit: conflictMin) {
                            L.push_back(-lit);
                            if(_weight[abs(lit)] < minWeight) {
                                minWeight = _weight[abs(lit)];
                            }
                        }
                        assert(minWeight > 0);
                        for(auto lit: conflictMin) {

                            assert( mapWeight2Assum[_weight[abs(lit)]].count( lit ) );
                            mapWeight2Assum[_weight[abs(lit)]].erase( lit );
                            _weight[abs(lit)] -= minWeight;
                            if(_weight[abs(lit)] == 0) {
                                CL_LitToRelax.push(lit);
                            } else {
                                mapWeight2Assum[_weight[abs(lit)]].insert( lit );
                            }
                        }

                        if(conflictMin.size() > 1) {
                            CL_CardToAdd.push({L, true, minWeight});
                        }
                        if(firstSolve) {
                            apply_CL_LitToRelax();      // TODO : On mesure une amélioration en effectuant apply maintenent ?
                            apply_CL_CardToAdd();       // TODO : On mesure une amélioration en effectuant apply maintenent ?
                        }

                        // Removal of literals that are no longer soft from the assumptions
                        for(auto lit: conflictMin) {
                            if(_weight[abs(lit)] == 0) {
                                assert(_assumption.count(lit));
                                _assumption.erase(lit);
                            }
                        }

                        assert(minWeight > 0);
                        //t_weight minWeight = 1;
                        MonPrint("\t\t\tMain Thread: cost = ", cost, " + ", minWeight);
                        cost += minWeight;
                    }

                }

                while(CL_LitToUnrelax.size()) {
                    auto element = CL_LitToUnrelax.pop();
                    assert(element);
                    _assumption.insert(*element);
                    //std::cout << "reintegration de _weight["<<abs(*element)<<"] = " << _weight[abs(*element)] << std::endl ;
                }
            }
        }

    }


    void setTimeOutFast(unsigned int timeOutFastMinimize) {
        _timeOutFastMinimize = timeOutFastMinimize;
    }

    void setCoefMinimize(unsigned int coefMinimizeTime) {
        _coefMinimizeTime = coefMinimizeTime;
    }

    t_weight getCost() override {
        return cost;
    }

    bool getValue(unsigned int var) override {
        return solver->getValue(var);
    }


    virtual unsigned int newSoftVar(bool value, t_weight weight) override {
        if(weight > 1) {
            setIsWeightedVerif(); // TODO : remplacer par  mapWeight2Assum
        }
        _weight.push_back(weight);
        mapWeight2Assum[weight].insert( _weight.size()-1 );
        mapAssum2card.push_back(-1);
        model.push_back(value);
        //nbSoft++;

        int var = solver->newVar();
        assert(var == _weight.size()-1);

        return var;
    }


    virtual int newVar(bool decisionVar=true) override {
        _weight.push_back(0);
        mapAssum2card.push_back(-1);
        model.push_back(false);

        int var = solver->newVar(decisionVar);

        assert(var == _weight.size()-1);

        return var;
    }

    virtual bool isSoft(unsigned int var) override {
        return var < _weight.size() && _weight[var] > 0;
    }





    virtual void setVarSoft(unsigned int var, bool value, t_weight weight) override {
        //assert(weight==1);

        while(var > nVars()) {
            newVar();
        }

        if( _weight[var] == 0 ) {
           _weight[var] = weight;
           mapWeight2Assum[_weight[var]].insert( (value?1:-1)*var );
           model[var] = value;      // "value" is the sign but represented as a bool
        } else {
            // In the case of weighted formula


            if(model[var] == value) {

                assert( mapWeight2Assum[_weight[var]].count( (value?1:-1)*var ) );
                mapWeight2Assum[_weight[var]].erase( (value?1:-1)*var );

                _weight[var] += weight;
            } else {

                assert( mapWeight2Assum[_weight[var]].count( -(value?1:-1)*var ) );
                mapWeight2Assum[_weight[var]].erase( -(value?1:-1)*var );

                if( _weight[var] > weight ) {
                    _weight[var] -= weight;
                    cost += weight;
                } else if( _weight[var] < weight ) {
                    cost += _weight[var];
                    _weight[var] = weight - _weight[var];
                    model[var] = !model[var];
                } else { assert( _weight[var] == weight );
                    cost += _weight[var];
                    _weight[var] = 0;
                    //nbSoft--;
                }
            }
            if(_weight[var] > 1) {
                setIsWeightedVerif(); // TODO : remplacer par  mapWeight2Assum
            }
            if(_weight[var] > 0) {
                mapWeight2Assum[_weight[var]].insert( (model[var]?1:-1)*var );
            }
        }

    }

    virtual unsigned int nSoftVar() override {
        unsigned int result = 0;
        for(auto w: _weight)
            if(w!=0)
                result++;
        return result;
    }

private:



    bool fullMinimize(VirtualSAT* solverForMinimize, std::set<int> &conflict, std::vector<int> &uselessLit, long timeRef) {
        C_fullMinimize.pause(false);
        MaLib::Chrono chrono;
        bool minimum = true;

        int B = 1000;
        //int B = 10000;

        if(timeRef > 60000000) {
            timeRef = 60000000;  // Hyperparameter
        }

        std::vector<int> removable;
        MonPrint("\t\t\t\t\tfullMinimize: Calculer Removable....");
        for(auto it = conflict.begin(); it != conflict.end(); ++it) {
            auto lit = *it;

            switch(solverForMinimize->solveLimited(conflict, B, lit)) {
            case 0:
                minimum = false;
                [[fallthrough]];
            case 1:
                break;

            case -1:
                removable.push_back(lit);
                break;

            default:
                assert(false);
            }
        }
        MonPrint("\t\t\t\t\tfullMinimize: removable = ", removable.size(), "/", conflict.size());

        if(removable.size() <= 1) {
            uselessLit = removable;
            for(auto lit: uselessLit) {
                conflict.erase(lit);
            }
            return minimum;
        }

        int maxLoop = 10000;
        if(removable.size() < 8) {
            maxLoop = 2*std::tgamma(removable.size()); // Gamma function is like a factorial but for natural numbers
        }


        if(isWeighted()) {
            std::sort(removable.begin(), removable.end(), [&](int litA, int litB){
                return _weight[ abs(litA) ] < _weight[ abs(litB) ];
            });
        }

        chrono.tic();
        // Same thing as above but with shuffles and a nested loop to hopefully find more useless lits
        for(int i=0; i<maxLoop; i++) {
            std::set<int> wConflict = conflict;
            std::vector<int> tmp_uselessLit;
            for(auto lit: removable) {
                switch(solverForMinimize->solveLimited(wConflict, B, lit)) {
                    case 0:
                        minimum = false;
                        [[fallthrough]];
                    case 1:
                        break;

                    case -1:
                        wConflict.erase(lit);
                        tmp_uselessLit.push_back(lit);
                        break;

                    default:
                        assert(false);
                }
            }

            if(tmp_uselessLit.size() > uselessLit.size()) {
                MonPrint("\t\t\t\t\tfullMinimize: newBest: ", tmp_uselessLit.size(), " removes.");
                uselessLit = tmp_uselessLit;
            }

            if(uselessLit.size() >= removable.size()-1) {
                MonPrint("\t\t\t\t\tfullMinimize: Optimal trouvé.");
                break;
            }

            if((i>=2) // Au moins 3 loops
                    && (timeRef*(1+numberMinimizeThreadRunning) <= chrono.tac())) {
                MonPrint("\t\t\t\t\tfullMinimize: TimeOut after ", (i+1), " loops");
                break;
            }

            std::random_shuffle(removable.begin(), removable.end());
        }

        for(auto lit: uselessLit) {
            conflict.erase(lit);
        }

        C_fullMinimize.pause(true);
        return minimum;
    }


    bool fastMinimize(VirtualSAT* solverForMinimize, std::list<int> &conflict) {
        C_fastMinimize.pause(false);

        if(isWeighted()) {
            conflict.sort([&](int litA, int litB){
                return _weight[ abs(litA) ] < _weight[ abs(litB) ];
            });
        }

        int B = 1;
        Chrono chrono;
        for(auto it = conflict.begin(); it != conflict.end(); ++it) {

            if(chrono.tacSec() > _timeOutFastMinimize) {  // Hyperparameter
                MonPrint("TIMEOUT fastMinimize!");
                C_fastMinimize.pause(true);
                return false;
            }

            auto lit = *it;
            it = conflict.erase(it);
            switch(solverForMinimize->solveLimited(conflict, B)) {
            case 0:
                [[fallthrough]];
            case 1:
                it = conflict.insert(it, lit);
                break;

            case -1:
                break;

            default:
                assert(false);
            }
        }

        C_fastMinimize.pause(true);
        return true;
    }

    virtual bool isWeighted() override {
//        assert( isWeightedVerif() == (mapWeight2Assum.size() > 1));
        return mapWeight2Assum.size() > 1;
    }


    //////////////////////////////
    /// For weighted formula ////
    ////////////////////////////

    bool getValueImpliesByAssign(unsigned int var) {
        if(_weight[var] == 0) {
            return getValue(var);
        }
        if( mapAssum2card[var] == -1 ) {
            if(mapSoft2clause.count(var) == 0) {
                assert(!"possible ?"); // La soft variable n'est ni une card ni une soft clause
                return getValue(var);
            } else {
                for(auto lit: mapSoft2clause[var]) {
                    //if( solver->getValue( abs(lit) ) == (lit>0)  ) { // same
                    if( getValueImpliesByAssign( abs(lit) ) == (lit>0) ) {
                        return true;
                    }
                }
                return false;
            }
        }

        auto [card, k, w] = save_card[ mapAssum2card[var] ];

        unsigned int k2=1;
        for(;k2<=k;k2++) {
            if( std::abs( card->atMost(k2) ) == var ) {
                break;
            }
        }
        assert( k2 <= k );

        unsigned int sum=0;
        for(auto lit: card->getClause()) {
            if( getValueImpliesByAssign( abs(lit) ) == (lit>0) ) {
                sum++;
            }
        }

        return !(sum <= k2);
    }


    t_weight currentSolutionCost() {
        t_weight result = cost;

        assert(CL_CardToAdd.size() == 0);

        for(unsigned int var=1; var<_weight.size(); var++) {
            if(_weight[var] > 0) {
                if(getValueImpliesByAssign(var) != model[var]) {
                    result += _weight[var];

                    if( mapAssum2card[var] != -1 ) {
                        auto [card, k, w] = save_card[ mapAssum2card[var] ];

                        unsigned int sum=0;
                        for(auto lit: card->getClause()) {
                            if( getValueImpliesByAssign( abs(lit) ) == (lit>0) ) {
                                sum++;
                            }
                        }
                        assert(sum > k); // car la card n'est pas satisfaite

                        result += ((t_weight)(sum-k-1)) * w;
                    }
                }
            }
        }

        return result;
    }

    // All soft variables whose cost is higher than the current solution can be considered as hard.
    unsigned int harden() {
        unsigned int nbHarden=0;

        auto costRemovedAssumLOCAL = currentSolutionCost();


        assert([&](){
            std::vector<bool> assign;
            assign.push_back(0); // fake var_0
            for(unsigned int i=1; i<=nInputVars; i++) {
                assign.push_back(getValue(i));
            }

            return costRemovedAssumLOCAL == calculateCost(savePourTest_file, assign);
        }());


        costRemovedAssumLOCAL -= cost;


        for(auto it = _assumption.begin(); it != _assumption.end(); ) {
            int lit = *it;
            ++it; // We increment "it" here beacause addClause({lit}) will remove lit from assumption
            if( _weight[ abs(lit) ] >= costRemovedAssumLOCAL ) {
                nbHarden++;
                addClause({lit});
            }
        }

        if(nbHarden) {
            std::cout << nbHarden << " HARDEN !!!!" << std::endl;
        }

        return nbHarden;
    }


};



EvalMaxSAT::~EvalMaxSAT() {
    CL_ConflictToMinimize.close();
    CL_LitToUnrelax.close();
    CL_LitToRelax.close();
    CL_CardToAdd.close();

    delete solver;
    for(auto s: solverForMinimize) {
        delete s;
    }
}



#endif // EVALMAXSAT_SLK178903R_H
