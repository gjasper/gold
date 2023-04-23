#include <iostream>
#include <vector>
#include <regex>
#include <algorithm>
#include <string>
#include <sstream>
#include <iomanip>

const int CLAUSE_SIZE = 3;
const int VARS_COUNT = 4;

class Clause {

    private:
        std::vector<std::pair<unsigned int, bool>> vars;
    public:
        Clause(std::string vs, std::string ss) {
            vars.insert(vars.begin() + 0, std::pair((int) vs.at(0) - 48, (int) ss.at(0) - 48));
            vars.insert(vars.begin() + 1, std::pair((int) vs.at(1) - 48, (int) ss.at(1) - 48));
            vars.insert(vars.begin() + 2, std::pair((int) vs.at(2) - 48, (int) ss.at(2) - 48));
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

        bool isClauseActive(int i){
            return activeClauses[cells[i].clause - 1];
        };

        bool isLiteralActive(int i){
            return activeLiterals[cells[i].literal];
        };

        int snext(int i){
            if(cells[i].next < 10 || (isClauseActive(cells[i].next) && (i < 10 || isLiteralActive(i)))){
                return cells[i].next;
            } else {
                return snext(cells[i].next);
            }
        }

        int sprev(int i){
            if(cells[i].prev < 10 || (isClauseActive(cells[i].prev) && (i < 10 || isLiteralActive(i)))){
                return cells[i].prev;
            } else {
                return sprev(cells[i].prev);
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
        AlgoA(std::vector<Clause> cs, std::vector<Cell> csls) :
            activeClauses(cs.size()), activeLiterals(VARS_COUNT * 2 + 2), cells(csls) {}
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

    public:
        SatModel(unsigned int varsQtt, std::string vs, std::string ss);
        std::vector<Clause> getClauses() {
            return clauses;
        }
        std::vector<Cell> getCells() {
            return cells;
        }
        bool isSat() {
            AlgoA a(clauses, cells);
            return a.run();
        }
        void print();
};