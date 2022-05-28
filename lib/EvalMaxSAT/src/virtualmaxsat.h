#ifndef VIRTUALMAXSAT_H
#define VIRTUALMAXSAT_H

#include <vector>
#include "virtualsat.h"
#include <set>
#include <fstream>
#include "../../cadical/src/cadical.hpp"
#include "../../cadical/src/file.hpp"
#include "ParseUtils.h"


typedef unsigned long long int t_weight;

class VirtualMAXSAT : public VirtualSAT {
public:

    virtual ~VirtualMAXSAT();

    virtual unsigned int newSoftVar(bool value, t_weight weight) = 0;

    virtual bool isSoft(unsigned int var) = 0;

    virtual void setVarSoft(unsigned int var, bool value, t_weight weight=1) = 0;

    virtual t_weight getCost() = 0;

    virtual void setNInputVars(unsigned int nb) = 0;

    int addWeightedClause(std::vector<int> clause, t_weight weight) {
        assert(weight==1);
        // If it's a unit clause and its literal doesn't exist as a soft var already, add soft variable
        if(clause.size() == 1) {
            if(!isSoft(abs(clause[0]))) {
                // The weight is zero by default (for hard vars), change it to the right weight if it's a soft var
                setVarSoft(abs(clause[0]), clause[0] > 0, weight);

                // Return instantly instead of adding a new var at the end because the soft var represents the unit clause anyway.
                // However, if the soft var already exists as soft, then we don't want to return as we want a new var to represent the 2nd clause.
                return 0;
            }
        }

        // Soft clauses are "hard" clauses with a soft var at the end. Create said soft var for our clause.
        int r = static_cast<int>(newSoftVar(true, weight));
        clause.push_back( -r );
        addClause(clause);
        clause.pop_back();

        return r;
    }

   std::vector<int> readClause(StreamBuffer &in) {
       std::vector<int> clause;

       for (;;) {
           int lit = parseInt(in);

           if (lit == 0)
               break;
           clause.push_back(lit);
           while( abs(lit) > nVars()) {
               newVar();
           }
       }

       return clause;
   }

   bool parse(gzFile in_) {
       StreamBuffer in(in_);

       if(*in == EOF) {
           return false;
       }

       std::vector < std::tuple < std::vector<int>, t_weight> > softClauses;

       for(;;) {
           skipWhitespace(in);

           if(*in == EOF) {
               break;
           }

           if(*in == 'c')
               skipLine(in);
           else {
               t_weight weight = parseInt64(in);
               std::vector<int> clause = readClause(in);

               if(weight == 0) {
                   addClause(clause);
               } else {
                   // If it is a soft clause, we have to save it to add it once we are sure we know the total number of variables.
                   softClauses.push_back({clause, weight});
               }
           }
       }

       for(auto & [clause, weight]: softClauses) {
           addWeightedClause(clause, weight);
       }

       return true;
    }

};
VirtualMAXSAT::~VirtualMAXSAT() {}

#endif // VIRTUALMAXSAT_H
