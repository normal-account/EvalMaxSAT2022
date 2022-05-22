
#include "virtualcard.h"

#include "virtualsat.h"

unsigned int VirtualCard::newVar(int lit) {
    solver->newVar(lit);
}

std::ostream& operator<<(std::ostream& os, const VirtualCard& dt) {
    dt.print(os);
    return os;
}


VirtualCard::~VirtualCard() {

}
