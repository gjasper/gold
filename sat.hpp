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

    class UNSAT : public std::exception {
    };

    class SAT : public std::exception {
    };

    private:
        std::vector<bool> activeClauses;
        std::vector<bool> activeLiterals;
        std::vector<Cell> cells;
        int a;
        int d;
        int l;
        std::vector<int> m;
        int varQtt;

        bool isClauseActive(int i) const {
            return activeClauses[cells.at(i).clause - 1];
        };

        bool isLiteralActive(int i) const {
            return activeLiterals.at(cells.at(i).literal);
        };

        int snext(int i) const {
            if(cells[i].next < (varQtt * 2 + 2) || (isClauseActive(cells.at(i).next) && (i < (varQtt * 2 + 2) || isLiteralActive(i)))){
                return cells.at(i).next;
            } else {
                return snext(cells.at(i).next);
            }
        }

        int sprev(int i) const {
            if(cells.at(i).prev < (varQtt * 2 + 2) || (isClauseActive(cells.at(i).prev) && (i < (varQtt * 2 + 2) || isLiteralActive(i)))){
                return cells.at(i).prev;
            } else {
                return sprev(cells.at(i).prev);
            }
        }

        void a1();
        void a2();
        void a3();
        void a4();
        void a5();
        void a6();
        void a7();
        void a8();

    public:
        AlgoA(std::vector<Clause> cs, std::vector<Cell> csls, int qtt) :
            a(cs.size()), activeLiterals(qtt * 2 + 2), cells(csls), varQtt(qtt) {}
        bool run(){
            try {
                a1();
            } catch(const SAT& e) {
                return true;
            } catch(const UNSAT& e) {
                return false;
            }
            return false;
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