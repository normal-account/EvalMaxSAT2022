/* This code is largely based on Genipamax from IPASIR
(https://github.com/biotomas/ipasir/tree/master/app/genipamax)
by Tomas Balyo, KIT, Karlsruhe. */
#include "pblib/pb2cnf.h"
#include "pblib/clausedatabase.h"
#include <vector>
#include <map>

using namespace std;
using namespace PBLib;

// The linked SAT solver might be written in C
extern "C" {
#include "ipasir.h"
}

/**
 * This class is used by the PBLib library to add clauses 
 * of the cardinality constraint to the solver. See the PBLib
 * documentation for more details.
 */
class IpasirClauseDatabase : public ClauseDatabase {
public:
	IpasirClauseDatabase(PBConfig config, void* solver):ClauseDatabase(config),solver(solver) {
	}
protected:
	void* solver;
	void addClauseIntern(const vector<int>& clause) {
		for (size_t i = 0; i < clause.size(); i++) {
			ipasir_add(solver, clause[i]);
		}
		ipasir_add(solver, 0);
	}
};

class IpamirSolver {

public:
    IpamirSolver() : n_vars(0) {}
    void add_hard(int32_t lit) {
        if (lit) clause.push_back(lit);
        else {
            hard_clauses.push_back(clause);
            clause.clear();
        }
    }
    void add_soft_lit(int32_t lit, uint64_t w) {
        soft_lits[lit] = w;
    }
    void assume(int32_t lit) {
        assumptions.push_back(lit);
    }
    int32_t solve() {
        void * solver = ipasir_init();
        n_vars = 0;
        assignment.clear();
        // add hard clauses to SAT solver
        for (auto const &clause : hard_clauses) {
            for (auto lit : clause) {
                ipasir_add(solver, lit);
                n_vars = max(n_vars, abs(lit));
                assignment[abs(lit)] = 0;
            }
            ipasir_add(solver, 0);
        }
        // add assumptions to SAT solver
        for (auto lit : assumptions) {
            ipasir_add(solver, lit);
            ipasir_add(solver, 0);
            n_vars = max(n_vars, abs(lit));
            assignment[abs(lit)] = 0;
        }
        assumptions.clear();
        int res = ipasir_solve(solver);
        // hard clauses are unsat
        if (res == 20) {
            ipasir_release(solver);
            return 20;
        }
        // calculate initial solution
        for (auto &[key, value] : assignment)
            value = ipasir_val(solver, key);
        // calculate cost of initial solution
        uint64_t cost = 0;
        vector<WeightedLit> lits;
        for (auto const &[lit, weight] : soft_lits) {
            n_vars = max(n_vars, abs(lit));
            assignment[abs(lit)] = ipasir_val(solver, lit);
            lits.push_back(WeightedLit(lit, weight));
            if (ipasir_val(solver, lit) == lit)
                cost += weight;
        }
        objective_value = cost;
        if (objective_value == 0) {
            ipasir_release(solver);
            return 30;
        }
        // PBLib initialization
        AuxVarManager avm(n_vars+1);
        PBConfig config = make_shared<PBConfigClass>();
        PB2CNF convertor(config);
        IpasirClauseDatabase icd(config, solver);
        // create the first cardinality constraint
        cost--;
        IncPBConstraint pbc(lits, LEQ, cost);
        convertor.encodeIncInital(pbc, icd, avm);
        // keep strengthening the bound and solving
        // until we reach an unsat formula.
        res = ipasir_solve(solver);
        while (res != 20) {
            for (auto &[key, value] : assignment)
                value = ipasir_val(solver, key);
            // calculate cost of last solution
            cost = 0;
            for (auto const &[lit, weight] : soft_lits)
                if (ipasir_val(solver, lit) == lit)
                    cost += weight;
            objective_value = cost;
            if (objective_value == 0)
                break;
            // strenghten the cardinality constraint
            cost--;
            pbc.encodeNewLeq(cost, icd, avm);
            res = ipasir_solve(solver);
        }
        ipasir_release(solver);
        return 30;
    }
    uint64_t val_obj() {
        return objective_value;
    }
    int32_t val_lit(int32_t lit) {
        return assignment[abs(lit)];
    }

private:
    int32_t n_vars;
    vector<int32_t> clause;
    vector<vector<int32_t>> hard_clauses;
    map<int32_t,uint64_t> soft_lits;
    vector<int32_t> assumptions;
    uint64_t objective_value;
    map<int32_t,int32_t> assignment;

};

extern "C" {

#include "ipamir.h"

static IpamirSolver * import (void * s) { return (IpamirSolver *) s; }

const char * ipamir_signature () { return "solver2022"; }
void * ipamir_init () { return new IpamirSolver(); }
void ipamir_release (void * s) { delete import(s); }
void ipamir_add_hard (void * s, int32_t l) { import(s)->add_hard(l); }
void ipamir_add_soft_lit (void * s, int32_t l, uint64_t w) { import(s)->add_soft_lit(l,w); }
void ipamir_assume (void * s, int32_t l) { import(s)->assume(l); }
int32_t ipamir_solve (void * s) { return import(s)->solve(); }
uint64_t ipamir_val_obj (void * s) { return import(s)->val_obj(); }
int32_t ipamir_val_lit (void * s, int32_t l) { return import(s)->val_lit(l); }
void ipamir_set_terminate (void * s, void * state, int (*terminate)(void * state)) {}

};