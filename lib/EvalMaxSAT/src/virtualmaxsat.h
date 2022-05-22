#ifndef VIRTUALMAXSAT_H
#define VIRTUALMAXSAT_H

#include <vector>
#include "virtualsat.h"
#include <set>
#include <fstream>
#include "../../cadical/src/cadical.hpp"
#include "../../cadical/src/file.hpp"
#include "ParseUtils.h"

class VirtualMAXSAT : public VirtualSAT {
public:
   int nVars = 0;
   std::vector < std::tuple < std::vector<int>, int> > softClauses;
   std::vector<std::vector<int>> hardClauses;


    virtual ~VirtualMAXSAT();

    virtual unsigned int newSoftVar(bool value, unsigned int weight) = 0;

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
                return 0;
            }
        }

        // Soft clauses are "hard" clauses with a soft var at the end. Create said soft var for our clause.
        int r = static_cast<int>(newSoftVar(true, weight));

        return r;
    }


   void addAllClauses() {
       for (int i = 0; i < nVars; i++)
           pushVar();

       for (auto &hardClause : hardClauses) {
           for (int j : hardClause) {
               newVar(j);
           }
           newVar(0);
       }

       for (auto &softTuple : softClauses) {
           std::vector<int> &softClause = std::get<0>(softTuple);

           int softVar = addWeightedClause(softClause, std::get<1>(softTuple));
           if (softVar) {
               for (int var : softClause) {
                   newVar(var);
               }

               newVar(-softVar);
               newVar(0);
           }

       }
       hardClauses.clear();
       softClauses.clear();
   }

   void readClause(StreamBuffer &in, std::vector<int> &lits) {
       int lit;
       for (;;) {
           lit = parseInt(in);

           if (lit == 0)
               break;
           lits.push_back(lit);
           if (abs(lit) > nVars)
               nVars = abs(lit);
       }
   }

   bool parse(gzFile in_) {
       StreamBuffer in(in_);

       std::vector<int> lits;
       int count = 0;
       for(;;) {
           skipWhitespace(in);

           if(*in == EOF)
           {
               addAllClauses();
               return true;
           }

           if(*in == 'c')
               skipLine(in);
           else {
               count++;
               lits.clear();

               int weight = parseInt64(in);

               readClause(in, lits);

               if(weight == 0) {
                   hardClauses.push_back(lits);
               } else {
                   softClauses.push_back( {lits, weight} );
               }
           }
       }
    }

};
VirtualMAXSAT::~VirtualMAXSAT() {}

#endif // VIRTUALMAXSAT_H
