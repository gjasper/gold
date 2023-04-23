#include <vector>
#include <string>
#include <cstdlib>

const int CLAUSE_SIZE = 3;

class Clause {

    private:
        std::vector<std::pair<unsigned int, bool>> vars;
    public:
        Clause(std::vector<int> vs){
            vars.insert(vars.end(), std::pair(abs(vs.at(0)), vs.at(0) > 0));
            vars.insert(vars.end(), std::pair(abs(vs.at(1)), vs.at(1) > 0));
            vars.insert(vars.end(), std::pair(abs(vs.at(2)), vs.at(2) > 0));
        }
        Clause(std::string vs, std::string ss){
            vars.insert(vars.end(), std::pair((int) vs.at(0) - 48, (int) ss.at(0) - 48));
            vars.insert(vars.end(), std::pair((int) vs.at(1) - 48, (int) ss.at(1) - 48));
            vars.insert(vars.end(), std::pair((int) vs.at(2) - 48, (int) ss.at(2) - 48));
        }
        std::vector<std::pair<unsigned int, bool>> getVars(){
            return vars;
        }
};

class Cell {

    private:
    public:
        Cell(): literal(0), next(0), prev(0), clause(0){}
        unsigned int next;
        unsigned int prev;
        unsigned int literal;
        unsigned int clause;
};

class AlgoA {

    public:
        AlgoA(std::vector<Clause> cs, std::vector<Cell> csls, int qtt) :
            activeClauses(cs.size()), activeLiterals(qtt * 2 + 2), cells(csls), varQtt(qtt) {}

        bool run(){
            NextStep nextStep = A1;
            while(true) {
                switch (nextStep) {
                    case A1: nextStep = a1(); break;
                    case A2: nextStep = a2(); break;
                    case A3: nextStep = a3(); break;
                    case A4: nextStep = a4(); break;
                    case A5: nextStep = a5(); break;
                    case A6: nextStep = a6(); break;
                    case A7: nextStep = a7(); break;
                    case A8: nextStep = a8(); break;
                    case RETURN_SAT: return true;
                    case RETURN_UNSAT: return false;
                }
            }
            return false;
        }

    private:

        enum NextStep {
            A1,
            A2,
            A3,
            A4,
            A5,
            A6,
            A7,
            A8,
            RETURN_SAT,
            RETURN_UNSAT
        };

        std::vector<bool> activeClauses;
        std::vector<bool> activeLiterals;
        std::vector<Cell> cells;
        unsigned int a;
        unsigned int d;
        unsigned int l;
        std::vector<int> m;
        unsigned int varQtt;

        NextStep a1();
        NextStep a2();
        NextStep a3();
        NextStep a4();
        NextStep a5();
        NextStep a6();
        NextStep a7();
        NextStep a8();

        void printM(){
            for (int i: m)
                std::cout << i;
            std::cout << std::endl;
        }

        bool isClauseActive(int i) const {
            return activeClauses.at(cells.at(i).clause - 1);
        };

        bool isLiteralActive(int i) const {
            return activeLiterals.at(cells.at(i).literal);
        };

        int snext(unsigned int i) const {
            if(cells[i].next < (varQtt * 2 + 2) || (isClauseActive(cells.at(i).next) && (i < (varQtt * 2 + 2) || isLiteralActive(i)))){
                return cells.at(i).next;
            } else {
                return snext(cells.at(i).next);
            }
        }

        int sprev(unsigned int i) const {
            if(cells.at(i).prev < (varQtt * 2 + 2) || (isClauseActive(cells.at(i).prev) && (i < (varQtt * 2 + 2) || isLiteralActive(i)))){
                return cells.at(i).prev;
            } else {
                return sprev(cells.at(i).prev);
            }
        }
};

class SatModel {

    private:
        std::vector<Clause> clauses;
        std::vector<Cell> cells;
        unsigned int varsQtt;

    public:
        SatModel(std::vector<Clause> cls, std::vector<Cell> cs, unsigned int qtt):
            clauses(cls), cells(cs), varsQtt(qtt) {};
        std::vector<Clause> getClauses() const {
            return clauses;
        }
        std::vector<Cell> getCells() const {
            return cells;
        }
        unsigned int getVarQtt() const {
            return varsQtt;
        }
        bool isSat() const {
            AlgoA a(clauses, cells, varsQtt);
            return a.run();
        }
        void print() const;
};

SatModel parseString(unsigned int, std::string, std::string);
SatModel parseDimacs(std::string);