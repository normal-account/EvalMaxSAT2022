#ifndef CADICALINTERFACE_H
#define CADICALINTERFACE_H

#include "virtualsat.h"

#include "../../cadical/src/cadical.hpp"

#include "coutUtil.h"
#include "Chrono.h"

#include <thread>
#include <future>
#include <iostream>
#include <chrono>



class CadicalInterface : public VirtualSAT {
    CaDiCaL::Solver *solver;
    int conflictSize;
    CadicalInterface( CaDiCaL::Solver* solver)
        : solver(solver) {
    }
public:

    CadicalInterface()
        : solver(new CaDiCaL::Solver()) {
    }
    
    VirtualSAT* clone() override {
        CaDiCaL::Solver *copySolver = new CaDiCaL::Solver;
        solver->copy(*copySolver);
        
        return new CadicalInterface(copySolver);
    }

    ~CadicalInterface() override;

   // For a given unit clause to have the passed value, give the required value for every other concerned literal
   // or return false if there is no solution
    bool propagate(const std::vector<int> &assum, std::vector<int> &result) override {
        return solver->find_up_implicants(assum, result);
    }

    void addUnitClause( int lit ) override {
        solver->add( lit );
        solver->add(0);
    }

   virtual void addClause( std::vector<int> &clause ) {
        for (int lit : clause)
            solver->add(lit);
       solver->add(0);
   }

   bool solve() override {
        bool result = solver->solve();
        return result;
    }

    std::vector<int> getConflict(const std::vector<int> &assumptions) override {
        std::vector<int> conflicts;
        int nConflicts = 0;
        for (int assumption : assumptions) {
            if (solver->failed(assumption)) {
                nConflicts++;
                conflicts.push_back(assumption);
            }
        }
        conflictSize = nConflicts;
        return conflicts;
    }

    // There is no method to get the size of the conflict in Cadical - hotfix
    unsigned int sizeConflict() override {
        return conflictSize;
    }

    int solveLimited(const std::vector<int> &assumption, int confBudget, int except=0) override {

        solver->reset_assumptions();

        for (int lit : assumption) {
            if (lit == except)
                continue;
            solver->assume(lit);
        }

        solver->limit("conflicts", confBudget);

        auto result = solver->solve();

        // TODO: Fix these hardcoded values for enums...
        if(result==10) { // Satisfiable
            return 1;
        }
        if(result==20) { // Unsatisfiable
            return -1;
        }
        if(result==0) { // Limit
            return 0;
        }

        assert(false);
    }

    int solveLimited(const std::list<int> &assumption, int confBudget, int except=0) override {
        solver->reset_assumptions();

        for (int lit : assumption) {
            if (lit == except)
                continue;
            solver->assume(lit);
        }

        solver->limit("conflicts", confBudget);

        auto result = solver->solve();

        if(result==10) { // Satisfiable
            return 1;
        }
        if(result==20) { // Unsatisfiable
            return -1;
        }
        if(result==0) { // Limit
            return 0;
        }

        assert(false);
    }


    int solveLimited(const std::set<int> &assumption, int confBudget, int except) override {
        solver->reset_assumptions();

        for (int lit : assumption) {
            if (lit == except)
                continue;
            solver->assume(lit);
        }

        solver->limit("conflicts", confBudget);

        auto result = solver->solve();

        if(result==10) { // Satisfiable
            return 1;
        }
        if(result==20) { // Unsatisfiable
            return -1;
        }
        if(result==0) { // Limit
            return 0;
        }

        assert(false);
    }

    bool solve(const std::vector<int> &assumption) override {
        for (int lit : assumption) {
            solver->assume(lit);
        }

        int result = solver->solve();

        return result == 10; // Sat
    }

    bool getValue(unsigned int var) override {
        return (solver->val(var) > 0);
    }

    void newVar(int lit) override {
        solver->add(lit);
    }
};
CadicalInterface::~CadicalInterface() {
    delete solver;
}


#endif
