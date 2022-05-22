#ifndef VIRTUALSAT_H
#define VIRTUALSAT_H

#include <vector>
#include <cmath>
#include <algorithm>
#include <cassert>
#include <memory>
#include <iostream>

#include "cardincremental.h"
#include "card_oe.h"
#include "lazyvariable.h"
#include "coutUtil.h"

using namespace MaLib;

class VirtualSAT {
public:

    virtual ~VirtualSAT();

    virtual VirtualSAT* clone() {assert(!"TODO");}

    virtual void addUnitClause( int lit )  {assert( !"TODO");}

    virtual void addClause( std::vector<int> &clause )  {assert( !"TODO");}

    virtual unsigned int nSoftVar() {assert(!"TODO");}

    virtual bool solve() {assert(!"TODO");}

    virtual bool propagate(const std::vector<int> &assum, std::vector<int> &result) {assert(!"TODO");}

    virtual bool solve(const std::vector<int> &assumption)  {assert(!"TODO");}

    virtual int solveLimited(const std::vector<int> &assumption, int confBudget, int except=0)  {assert(!"TODO");}

    virtual int solveLimited(const std::list<int> &assumption, int confBudget, int except=0)  {assert(!"TODO");}

    virtual int solveLimited(const std::set<int> &assumption, int confBudget, int except=0)  {assert(!"TODO");}

    virtual bool getValue(unsigned int var)  {assert(!"TODO");} // TODO: unsigned int

    virtual void newVar(int lit) {assert(!"TODO");}

    virtual unsigned int newSoftVar(bool value, unsigned int weight) {assert(!"TODO");}

    virtual void pushVar() {assert(!"TODO");}

    virtual unsigned int sizeConflict() {assert(!"TODO");}

    virtual std::vector<int> getConflict(const std::vector<int>& assumptions  )  {assert(!"TODO");}

    std::shared_ptr<VirtualCard> newCard(const std::vector<int> &clause, unsigned int bound=1) {
        return std::make_shared<CardIncremental_Lazy>(this, clause, bound);
    }

    std::shared_ptr<LazyVariable> newLazyVariable() {
        return LazyVariable::newVar(this);
    }


};



#endif // VIRTUALSAT_H
