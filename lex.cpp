#include <iostream>
#include <vector>
#include <string>
#include<stack>
#include<unordered_map>
#include<set>
#include<map>
#include<queue>

using namespace std;
typedef set<int> StateSet;
StateSet trap;
class CFG {
public:
    vector<char> terminals; // 终结符号
    vector<char> nonTerminals; // 非终结符号
    char startSymbol; // 起始符号
    unordered_map<char, string> productions; // 产生式

    CFG() : startSymbol('S') {
        terminals.push_back('#'); // 这里以#作为空字符
    }

    bool isTerminals(char c) {
        auto it = find(terminals.begin(), terminals.end(), c);
        return it != terminals.end();
    }

    bool isNonTerminals(char c) {
        auto it = find(nonTerminals.begin(), nonTerminals.end(), c);
        return it != nonTerminals.end();
    }

    bool allTerminals(char left) {
        string right = productions[left];
        for (char c : right) {
            if (isNonTerminals(c))
                return false;
        }
        return true;
    }

    void showProductions() {
        for (auto it : productions) {
            char left = it.first;
            string right = it.second;
            cout << left << " -> " << right << endl;
        }
    }

    void removeNonTerminals(char c) {
        productions.erase(productions.find(c));
        nonTerminals.erase(find(nonTerminals.begin(), nonTerminals.end(), c));
    }
};

bool isOperator(char c) {
    return c == '.' || c == '|' || c == '*';
}

void printSet(set<int> s, string end = "\n") {
    for (int i : s)
        cout << i << ' ';
    cout << end;
}

string addConSym(string s) {
    string res;
    for (int i = 0; i < s.size() - 1; i++) {
        string temp = s.substr(i, 1);
        if ((s.at(i) == ')' || s.at(i) == '*' || isalpha(s.at(i))) &&
            (s.at(i + 1) == '(' || isalpha(s.at(i + 1)))) {
            temp += ".";
        }
        res += temp;
    }
    res += s.back();
        return res;
}

string infixToPostfix(string infix) {
    stack<char> s;
    string postfix = "";
    unordered_map<char, int> precedence;

    precedence['|'] = 1;
    precedence['.'] = 2;
    precedence['*'] = 3;

    for (char c : infix) {
        if (isalpha(c)) {
            postfix += c;
        }
        else if (c == '(') {
            s.push(c);
        }
        else if (c == ')') {
            while (!s.empty() && s.top() != '(') {
                postfix += s.top();
                s.pop();
            }
            s.pop();
        }
        else if (isOperator(c)) {
            while (!s.empty() && precedence[c] <= precedence[s.top()]) {
                postfix += s.top();
                s.pop();
            }
            s.push(c);
        }
    }

    while (!s.empty()) {
        postfix += s.top();
        s.pop();
    }

    return postfix;
}

CFG regexToCFG(string postfix) {
    stack<char> s;
    CFG cfg;

    for (char c : postfix) {
        if (!isOperator(c)) {
            auto it = find(cfg.terminals.begin(), cfg.terminals.end(), c);
            if (it == cfg.terminals.end())
                cfg.terminals.push_back(c);
        }
    }

    for (char c : postfix) {
        string right;
        if (!isOperator(c)) {
            s.push(c);
            continue;
        }
        else if (c == '*') {
            char sym = s.top();
            s.pop();
            right = string(1, sym) + string(1, c);
        }
        else {
            char sym2 = s.top();
            s.pop();
            char sym1 = s.top();
            s.pop();
            right = string(1, sym1) + string(1, c) + string(1, sym2);
        }

        char left = 'A' + cfg.nonTerminals.size();
        cfg.nonTerminals.push_back(left);
        if (s.empty())
            cfg.productions['S'] = string(1, left);
        s.push(left);
        cfg.productions[left] = right;
    }

    return cfg;
}



class NFA {
public:
    set<int> states;
    map<pair<int, char>, StateSet> transitions;
    set<char> inputs;
    int startState;
    set<int> acceptStates;

    NFA() {}

    void addState(int state) {
        states.insert(state);
    }

    void addTransition(int from, char input, int to) {
        transitions[make_pair(from, input)].insert(to);
        inputs.insert(input);
    }

    void setStartState(int state) {
        startState = state;
    }

    void addAcceptState(int state) {
        acceptStates.insert(state);
    }

    StateSet getEpsilonClosure(int state) {
        StateSet closure;
        stack<int> st;
        st.push(state);
        while (!st.empty()) {
            int s = st.top();
            st.pop();
            closure.insert(s);
            for (int nextState : transitions[make_pair(s, ' ')]) {
                if (closure.find(nextState) == closure.end()) {
                    st.push(nextState);
                }
            }
        }
        return closure;
    }

    StateSet getEpsilonClosure(StateSet states) {
        StateSet closure;
        for (int state : states) {
            StateSet s = getEpsilonClosure(state);
            closure.insert(s.begin(), s.end());
        }
        return closure;
    }

    StateSet move(StateSet states, char input) {
        StateSet nextStates;
        for (int state : states) {
            StateSet s = transitions[make_pair(state, input)];
            nextStates.insert(s.begin(), s.end());
        }
        return nextStates;
    }

    bool accept(string input) {
        StateSet currentStates = getEpsilonClosure(startState);
        for (char c : input) {
            currentStates = getEpsilonClosure(move(currentStates, c));
        }
        return any_of(currentStates.begin(), currentStates.end(), [this](int state) {
            return acceptStates.find(state) != acceptStates.end();
            });
    }

    void showTransitions() {
        for (const auto& it : transitions) {
            const StateSet& to = it.second;
            for (int seti : to) {
                if (it.first.second == ' ')
                    cout << it.first.first << " # " << seti << endl;
                else
                    cout << it.first.first << ' ' << it.first.second << ' ' << seti << endl;
            }
        }
    }
};


NFA CFG2NFA(CFG cfg)
{
    //CFG符号到子NFA状态(起始状态+终止状态)的映射
    unordered_map<char, vector<int>> symToState;
    NFA nfa;
    while (!cfg.nonTerminals.empty())
    {
        char left;
        string right;
        //遍历查找全为终结符的产生式右部
        for (auto it : cfg.productions)
        {
            if (cfg.allTerminals(it.first))
            {
                left = it.first;
                right = it.second;
                break;
            }
        }
        //如果一个符号的右部全为终结符，将该符号标记为终结符
        cfg.removeNonTerminals(left);
        //cout << right << endl;
        char oper = right.at(1);
        //根据运算符，添加状态、转移函数
        switch (oper)
        {
        case '.':
        {
            int s0, s1, s2, s3;
            char sym1 = right.at(0);
            char sym2 = right.at(2);
            if (symToState.find(sym1) == symToState.end())
            {
                //都是终结符
                if (symToState.find(sym2) == symToState.end())
                {
                    s0 = nfa.states.size();
                    s1 = s0 + 1;
                    s2 = s0 + 2;
                    s3 = s0 + 3;
                    nfa.states.insert({ s0, s1, s2, s3 });
                    nfa.addTransition(s0, sym1, s1);
                    nfa.addTransition(s1, ' ', s2);
                    nfa.addTransition(s2, sym2, s3);
                }
                //左边是终结符，右边是非终结符
                else
                {

                    s0 = nfa.states.size();
                    s1 = s0 + 1;
                    nfa.states.insert({ s0, s1 });
                    s2 = symToState[sym2][0];
                    s3 = symToState[sym2][1];
                    nfa.addTransition(s0, sym1, s1);
                    nfa.addTransition(s1, ' ', s2);
                }
            }
            else
            {
                //左边是非终结符，右边是终结符
                if (symToState.find(sym2) == symToState.end())
                {
                    s0 = symToState[sym1][0];
                    s1 = symToState[sym1][1];
                    s2 = nfa.states.size();
                    s3 = s2 + 1;
                    nfa.states.insert({ s2, s3 });
                    nfa.addTransition(s1, ' ', s2);
                    nfa.addTransition(s2, sym2, s3);
                }
                //两边都是非终结符
                else
                {
                    s0 = symToState[sym1][0];
                    s1 = symToState[sym1][1];
                    s2 = symToState[sym2][0];
                    s3 = symToState[sym2][1];
                    nfa.addTransition(s1, ' ', s2);
                }
            }
            symToState[left] = vector<int>{ s0, s3 };
            break;
        }
        case '|':
        {
            int s0, s1, s2, s3, s4, s5;
            char sym1 = right.at(0);
            char sym2 = right.at(2);
            if (symToState.find(sym1) == symToState.end())
            {
                //都是终结符
                if (symToState.find(sym2) == symToState.end())
                {
                    s0 = nfa.states.size();
                    s1 = s0 + 1;
                    s2 = s0 + 2;
                    s3 = s0 + 3;
                    s4 = s0 + 4;
                    s5 = s0 + 5;
                    nfa.states.insert({ s0,s1,s2,s3,s4,s5 });
                    nfa.addTransition(s0, ' ', s1);
                    nfa.addTransition(s1, sym1, s2);
                    nfa.addTransition(s2, ' ', s5);
                    nfa.addTransition(s0, ' ', s3);
                    nfa.addTransition(s3, sym2, s4);
                    nfa.addTransition(s4, ' ', s5);
                }
                //左边是终结符，右边是非终结符
                else
                {
                    s0 = nfa.states.size();
                    s1 = s0 + 1;
                    s2 = s0 + 2;
                    s3 = symToState[sym2][0];
                    s4 = symToState[sym2][1];
                    s5 = s0 + 3;
                    nfa.states.insert({ s0, s1, s2, s5 });
                    nfa.addTransition(s0, ' ', s1);
                    nfa.addTransition(s1, sym1, s2);
                    nfa.addTransition(s2, ' ', s5);
                    nfa.addTransition(s0, ' ', s3);
                    nfa.addTransition(s4, ' ', s5);
                }
            }
            else
            {
                //左边是非终结符，右边是终结符
                if (symToState.find(sym2) == symToState.end())
                {
                    s0 = nfa.states.size();
                    s1 = symToState[sym1][0];
                    s2 = symToState[sym1][1];
                    s3 = s0 + 1;
                    s4 = s0 + 2;
                    s5 = s0 + 3;
                    nfa.states.insert({ s0, s3, s4, s5 });
                    nfa.addTransition(s0, ' ', s1);
                    nfa.addTransition(s2, ' ', s5);
                    nfa.addTransition(s0, ' ', s3);
                    nfa.addTransition(s3, sym2, s4);
                    nfa.addTransition(s4, ' ', s5);
                }
                //两边都是非终结符
                else
                {
                    s0 = nfa.states.size();
                    s1 = symToState[sym1][0];
                    s2 = symToState[sym1][1];
                    s3 = symToState[sym2][0];
                    s4 = symToState[sym2][1];
                    s5 = s0 + 1;
                    nfa.states.insert({ s0, s1 });
                    nfa.addTransition(s0, ' ', s1);
                    nfa.addTransition(s2, ' ', s5);
                    nfa.addTransition(s0, ' ', s3);
                    nfa.addTransition(s4, ' ', s5);
                }
            }
            symToState[left] = vector<int>{ s0, s5 };
            break;
        }
        case '*':
        {
            int s0, s1, s2, s3;
            char sym = right.at(0);
            //sym是终结符
            if (symToState.find(sym) == symToState.end())
            {
                s0 = nfa.states.size();
                s1 = s0 + 1;
                s2 = s0 + 2;
                s3 = s0 + 3;
                nfa.states.insert({ s0, s1, s2, s3 });
                nfa.addTransition(s0, ' ', s1);
                nfa.addTransition(s1, sym, s2);
                nfa.addTransition(s2, ' ', s3);
                nfa.addTransition(s0, ' ', s3);
                nfa.addTransition(s2, ' ', s1);
            }
            //sym是非终结符
            else
            {
                s0 = nfa.states.size();
                s1 = symToState[sym][0];
                s2 = symToState[sym][1];
                s3 = s0 + 1;
                nfa.states.insert({ s0, s3 });
                nfa.addTransition(s0, ' ', s1);
                nfa.addTransition(s2, ' ', s1);
                nfa.addTransition(s2, ' ', s3);
                nfa.addTransition(s0, ' ', s3);
            }
            symToState[left] = vector<int>{ s0, s3 };
            break;
        }
        }
        if (cfg.nonTerminals.empty())
        {
            nfa.setStartState(symToState[left][0]);
            nfa.addAcceptState(symToState[left][1]);
        }
    }
    return nfa;
}
class DFA {
public:
    set<StateSet> states;
    map<pair<StateSet, char>, StateSet> transitions;
    StateSet startState;
    set<StateSet> acceptStates;
    set<char> inputs;

    void addState(StateSet state) {
        states.insert(state);
    }

    void addAcceptState(StateSet state) {
        acceptStates.insert(state);
    }

    void addTransition(StateSet from, char input, StateSet to) {
        // 防止重复添加转移
        transitions[make_pair(from, input)] = to;
        inputs.insert(input);
    }

    void showTransitions(bool simplify = false) {
        if (simplify) {
            map<StateSet, int> newState;

            for (const auto& it : transitions) {
                const StateSet& from = it.first.first;
                char input = it.first.second;
                const StateSet& to = it.second;

                if (newState.find(from) == newState.end()) {
                    newState[from] = newState.size();
                }
                int fromState = newState[from];

                if (newState.find(to) == newState.end()) {
                    newState[to] = newState.size();
                }
                int toState = newState[to];

                cout << "( " << fromState << ' ';
                if (input == ' ') {
                    cout << "# ";
                }
                else {
                    cout << input << ' ';
                }
                cout << toState << " )" << endl;
            }

            cout << endl << "old state -> new state: " << endl;
            for (const auto& it : newState) {
                cout << "( ";
                printSet(it.first, ")");
                cout << " -> " << it.second << endl;
            }
        }
        else {
            for (const auto& it : transitions) {
                const StateSet& from = it.first.first;
                char input = it.first.second;
                const StateSet& to = it.second;

                cout << "( ";
                printSet(from, ")");

                if (input == ' ') {
                    cout << " # ( ";
                }
                else {
                    cout << ' ' << input << " ( ";
                }

                printSet(to, ")\n");
            }
        }
    }
};

DFA NFA2DFA(NFA nfa) {
    DFA dfa;
    dfa.startState = nfa.getEpsilonClosure(nfa.startState);
    queue<StateSet> stateQueue;
    stateQueue.push(dfa.startState);

    while (!stateQueue.empty()) {
        StateSet curState = stateQueue.front();
        stateQueue.pop();

        dfa.addState(curState);

        // 如果当前状态是NFA的接受状态，那么也是DFA的接受状态
        for (int state : curState) {
            if (nfa.acceptStates.count(state)) {
                dfa.addAcceptState(curState);
                break;
            }
        }

        // 对于每个输入，计算下一状态集合
        for (char input : nfa.inputs) {
            if (input != ' ') {
                StateSet nextState = nfa.getEpsilonClosure(nfa.move(curState, input));

                if (nextState.empty()) {
                    dfa.addTransition(curState, input, trap);
                }
                else if (!nextState.empty()) {
                    dfa.addTransition(curState, input, nextState);

                    // 如果下一状态是新的，将其加入队列
                    if (!dfa.states.count(nextState)) {
                        stateQueue.push(nextState);
                    }
                }
            }
        }
    }

    return dfa;
}

DFA minDFA(DFA dfa)
{
    map<StateSet, int> equivalenceClasses;
    int currentClass = 2;

    // Initialize equivalence classes based on accept and non-accept states
    for (const StateSet& state : dfa.states) {
        equivalenceClasses[state] = dfa.acceptStates.count(state) > 0 ? 0 : 1;
    }

    bool changed = true;

    while (changed) {
        changed = false;

        for (char input : dfa.inputs) {
            for (int j = 0; j < currentClass; ++j) {
                map<int, int> prevClass;
                int num = 0;
                bool first = true;

                for (const StateSet& state : dfa.states) {
                    if (equivalenceClasses[state] != j) continue;

                    StateSet next = dfa.transitions[make_pair(state, input)];

                    if (next == trap) {
                        if (first) num++;
                        first = false;
                        continue;
                    }

                    int nextClass = equivalenceClasses[next];

                    if (prevClass.empty()) {
                        prevClass[nextClass] = j;
                        num++;
                    }
                    else if (prevClass.count(nextClass) == 0) {
                        prevClass[nextClass] = currentClass++;
                        num++;
                    }
                }

                if (num != 1) {
                    bool first = true;
                    map<StateSet, int> newEquivalenceClasses;

                    for (const StateSet& state : dfa.states) {
                        if (equivalenceClasses[state] != j) continue;

                        StateSet next = dfa.transitions[make_pair(state, input)];

                        if (next == trap) {
                            if (first) currentClass++;
                            newEquivalenceClasses[state] = currentClass - 1;
                            first = false;
                            continue;
                        }

                        int nextClass = equivalenceClasses[next];
                        newEquivalenceClasses[state] = prevClass[nextClass];
                    }

                    for (auto it = newEquivalenceClasses.begin(); it != newEquivalenceClasses.end(); ++it) {
                        equivalenceClasses[it->first] = it->second;
                    }

                    changed = true;
                }
            }
        }
    }

    equivalenceClasses[trap] = currentClass++;

    DFA minimizedDFA;
    map<int, StateSet> classToStateSet;

    for (const StateSet& state : dfa.states) {
        int eqClass = equivalenceClasses[state];

        if (classToStateSet.find(eqClass) == classToStateSet.end() || dfa.acceptStates.count(state) > 0) {
            classToStateSet[eqClass] = state;
        }
    }

    classToStateSet[currentClass - 1] = trap;
    set<int> s;

    for (const StateSet& state : dfa.states) {
        int eqClass = equivalenceClasses[state];

        if (s.count(eqClass) == 0) {
            minimizedDFA.addState(classToStateSet[eqClass]);

            if (classToStateSet[eqClass] == dfa.startState) {
                minimizedDFA.startState = classToStateSet[eqClass];
            }

            if (dfa.acceptStates.count(state) > 0) {
                minimizedDFA.addAcceptState(classToStateSet[eqClass]);
            }
        }

        for (char input : dfa.inputs) {
            StateSet nextState = dfa.transitions[make_pair(state, input)];
            int nextEqClass = equivalenceClasses[nextState];
            StateSet nextClassStateSet = classToStateSet[nextEqClass];
            minimizedDFA.addTransition(classToStateSet[eqClass], input, nextClassStateSet);
        }
    }

    return minimizedDFA;
}

int main()
{
    trap.insert(9999);
    string infix = "a.(b|c*).(d*|e.f)*";
    infix = addConSym(infix);
    string postfix = infixToPostfix(infix);
    CFG cfg = regexToCFG(postfix);
    NFA nfa = CFG2NFA(cfg);
    DFA dfa = NFA2DFA(nfa);
   DFA dfa2 = minDFA(dfa);
    cout << "Start: ";
    printSet(dfa.startState);
    cout << "Accept: " << endl;
    for (StateSet s : dfa.acceptStates)
    {
        printSet(s);
    }
    cout << endl;
    dfa.showTransitions(true);
    cout << "DFA最小化后" << endl;
    cout << "Start: ";
    printSet(dfa2.startState);
    cout << "Accept: " << endl;
    for (StateSet s : dfa2.acceptStates)
    {
        printSet(s);
    }
    cout << endl;
    dfa2.showTransitions(true);
    return 0;
}