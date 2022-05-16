#ifndef VIRTUALMAXSAT_H
#define VIRTUALMAXSAT_H

#include <vector>
#include "virtualsat.h"
#include <set>

#include "glucose/utils/ParseUtils.h"

class VirtualMAXSAT : public VirtualSAT {
public:
    std::vector<bool> literalPresent; // Where int is the var, and bool is whether it should be added as a soft var or not
   // Save clauses in a vector to add them to the solver after adding the variables
    std::vector<std::tuple<std::vector<int>, int>> softClauses;
    std::vector<std::vector<int>> hardClauses;

    virtual ~VirtualMAXSAT();

    virtual unsigned int newSoftVar(bool value, bool decisionVar, unsigned int weight) = 0;

    virtual bool isSoft(unsigned int var) = 0;

    virtual void setVarSoft(unsigned int var, bool value, unsigned int weight=1) = 0;

    virtual int getCost() = 0;

    virtual void setNInputVars(unsigned int nb) = 0;

    int addWeightedClause(std::vector<int> clause, unsigned int weight) {
        assert(weight==1);
        // If it's a unit clause and its literal doesn't exist as a soft var already, add soft variable
        if(clause.size() == 1) {
            if(!isSoft(abs(clause[0]))) {
                // The weight is zero by default (for hard vars), change it to the right weight if it's a soft var
                setVarSoft(abs(clause[0]), clause[0] > 0, weight);

                // Return instantly instead of adding a new var at the end because the soft var represents the unit clause anyway.
                // However, if the soft var already exists as soft, then we don't want to return as we want a new var to represent the 2nd clause.
                return clause[0];
            }
        }

        // Soft clauses are "hard" clauses with a soft var at the end. Create said soft var for our clause.
        int r = static_cast<int>(newSoftVar(true, false, weight));

        clause.push_back(-r);
        addClause(clause);

        return r;
    }

    void addAllLiterals () {
        for (int i = 0; i < literalPresent.size(); i++) {
            newVar();
        }
        literalPresent.clear();
    }

    void addAllClauses() {
        for (const auto& clause : hardClauses)
            addClause(clause);

        for (auto clauseTuple : softClauses)
            addWeightedClause(std::get<0>(clauseTuple), std::get<1>(clauseTuple));
        hardClauses.clear();
        softClauses.clear();
    }

    bool parse(gzFile in_) {

        Glucose::StreamBuffer in(in_);

        int64_t weight;

        std::vector<int> lits;
        int count = 0;
        for(;;) {
            Glucose::skipWhitespace(in);

            if(*in == EOF)
            {
                addAllLiterals();
                addAllClauses();
                break;
            }

            else if(*in == 'c')
                Glucose::skipLine(in);
            else {
                count++;

                weight = Glucose::parseInt64(in);

                readClause(in, lits);

                if(weight == 0) {
                    hardClauses.push_back(lits);
                } else {
                    softClauses.push_back( {lits, weight} );
                }
            }
        }

        return true;
    }

private:

    template<class B>
    void readClause(B& in, std::vector<int>& lits) {
        int parsed_lit;
        lits.clear();
        for (;;){
            parsed_lit = Glucose::parseInt(in);
            if (parsed_lit == 0) break;

            if ( abs(parsed_lit) >= literalPresent.size())  // TODO: REVISIT STRUCTURE
                literalPresent.resize(abs(parsed_lit));

            literalPresent[ abs(parsed_lit) ] = true;

            lits.push_back( parsed_lit );
        }
    }

};
VirtualMAXSAT::~VirtualMAXSAT() {}

#endif // VIRTUALMAXSAT_H
