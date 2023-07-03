#include<iostream>
#include<sstream>
#include<vector>
#include<string>
#include<set>
#include<stack>
#include <algorithm>
#include <iterator>
#include <map>
#include <string.h>
#define DEBUG 1

using namespace std;

string join(vector<int> v, string delim) {
    stringstream ss;
    for(int i = 0; i < v.size(); ++i) {
        if(i != 0)
            ss << ",";
        ss << v[i];
    }
    if (v.size())
        return ss.str();
    return "";
}

struct trans {
    int vertex_from;
    int vertex_to;
    char trans_symbol;
};


class NFA {
    public:
        vector<int> vertex;
        vector<trans> transitions;
        vector<char> symbol;
        int final_state;

        NFA() {

        }

        int get_vertex_count() {
            return vertex.size();
        }

        void set_vertex(int no_vertex) {
            for(int i = 0; i < no_vertex; i++) {
                vertex.push_back(i);
            }
        }

        void set_transition(int vertex_from, int vertex_to, char trans_symbol) {
            trans new_trans;
            new_trans.vertex_from = vertex_from;
            new_trans.vertex_to = vertex_to;
            new_trans.trans_symbol = trans_symbol;
            transitions.push_back(new_trans);
        }

        void set_final_state(int fs) {
            final_state = fs;
        }

        int get_final_state() {
            return final_state;
        }

        void display() {
            trans new_trans;
            cout<<"\n";
            for(int i = 0; i < transitions.size(); i++) {
                new_trans = transitions.at(i);
                cout<<"q"<<new_trans.vertex_from<<" -> q"<<new_trans.vertex_to<<" : Symbol - "<<new_trans.trans_symbol<<endl;
            }
            if (get_final_state()>=0) {
                cout<<"\nThe final state is q : "<<get_final_state()<<endl;
            } else {
                cout<<"\nnfa does not have a final state!"<<endl;
            }
        }

        /**
         * Get the set of reachable state from each specified vertex.
         */
        vector<char> find_possible_input_symbols(const vector<int>& vertexs) {
            vector<char> result;

            for (int i = 0; i < vertexs.size(); i++) {
                int vertex_from = vertexs.at(i);
                for (int j = 0; j < transitions.size(); j++) {
                    trans it = transitions.at(j);
                    if (it.vertex_from == vertex_from && it.trans_symbol != '^') {
                        result.push_back(it.trans_symbol);
                    }
                }
            }

            return result;
        }

        vector<int> eclosure(const vector<int>& X) {
            vector<int> result;
            vector<bool> visited (get_vertex_count(), false);

            for (int i = 0; i < X.size(); i++) {
                eclosure(X.at(i), result, visited);
            }

            sort(result.begin(), result.end());
            unique(result.begin(), result.end());
#ifdef DEBUG
            cout << "eclosure{" << join(X, ",") << "}  ->  "<< join(result, ",") << endl;
#endif
            return result;
        }

        void eclosure(int x, vector<int>& result, vector<bool>& visited) {
            result.push_back(x);

            for (int i = 0; i < transitions.size(); i++) {
                trans it = transitions.at(i);
                if (it.vertex_from == x && it.trans_symbol == '^') {
                    int y = it.vertex_to;
                    if (!visited.at(y)) {
                        visited.at(y) = true;
                        eclosure(y, result, visited);
                    }
                }
            }
        }

        vector<int> move(const vector<int>& T, const char trans_symbol) {
            vector<int> result;

            for (int j = 0; j < T.size(); j++) {
                int t = T.at(j);

                for (int i = 0; i < transitions.size(); i++) {
                    trans it = transitions.at(i);
                    if (it.vertex_from == t && it.trans_symbol == trans_symbol) {
                        result.push_back(it.vertex_to);
                    }
                }
            }

            sort(result.begin(), result.end());

#ifdef DEBUG
            int l1 = result.size();
            unique(result.begin(), result.end());
            int l2 = result.size();
            if (l2 < l1) {
                cerr << "move(T, a) return non-unique vector" << endl;
                exit(1);
            }
#endif

            return result;
        }

};

NFA concat(NFA a, NFA b) {
    NFA result;
    result.set_vertex(a.get_vertex_count() + b.get_vertex_count());
    int i;
    trans new_trans;

    for(i = 0; i < a.transitions.size(); i++) {
        new_trans = a.transitions.at(i);
        result.set_transition(new_trans.vertex_from, new_trans.vertex_to, new_trans.trans_symbol);
    }

    result.set_transition(a.get_final_state(), a.get_vertex_count(), '^');

    for(i = 0; i < b.transitions.size(); i++) {
        new_trans = b.transitions.at(i);
        result.set_transition(new_trans.vertex_from + a.get_vertex_count(), new_trans.vertex_to + a.get_vertex_count(), new_trans.trans_symbol);
    }

    result.set_final_state(a.get_vertex_count() + b.get_vertex_count() - 1);

    return result;
}


NFA kleene(NFA a) {
    NFA result;
    int i;
    trans new_trans;

    result.set_vertex(a.get_vertex_count() + 2);

    result.set_transition(0, 1, '^');

    for(i = 0; i < a.transitions.size(); i++) {
        new_trans = a.transitions.at(i);
        result.set_transition(new_trans.vertex_from + 1, new_trans.vertex_to + 1, new_trans.trans_symbol);
    }

    result.set_transition(a.get_vertex_count(), a.get_vertex_count() + 1, '^');
    result.set_transition(a.get_vertex_count(), 1, '^');
    result.set_transition(0, a.get_vertex_count() + 1, '^');

    result.set_final_state(a.get_vertex_count() + 1);

    return result;
}


NFA or_selection(vector<NFA> selections, int no_of_selections) {
    NFA result;
    int vertex_count = 2;
    int i, j;
    NFA med;
    trans new_trans;

    for(i = 0; i < no_of_selections; i++) {
        vertex_count += selections.at(i).get_vertex_count();
    }

    result.set_vertex(vertex_count);

    int adder_track = 1;

    for(i = 0; i < no_of_selections; i++) {
        result.set_transition(0, adder_track, '^');
        med = selections.at(i);
        for(j = 0; j < med.transitions.size(); j++) {
            new_trans = med.transitions.at(j);
            result.set_transition(new_trans.vertex_from + adder_track, new_trans.vertex_to + adder_track, new_trans.trans_symbol);
        }
        adder_track += med.get_vertex_count();

        result.set_transition(adder_track - 1, vertex_count - 1, '^');
    }

    result.set_final_state(vertex_count - 1);

    return result;
}


NFA re_to_nfa(string re) {
    stack<char> operators;
    stack<NFA> operands;
    char op_sym;
    int op_count;
    char cur_sym;
    NFA *new_sym;
    vector<char> sym;
    bool let;

    for(string::iterator it = re.begin(); it != re.end(); ++it) {
        let=false;
        cur_sym = *it;
        if(cur_sym != '(' && cur_sym != ')' && cur_sym != '*' && cur_sym != '+' && cur_sym != '.') {
            new_sym = new NFA();
            new_sym->set_vertex(2);
            new_sym->set_transition(0, 1, cur_sym);
            new_sym->set_final_state(1);
            operands.push(*new_sym);
            delete new_sym;
            for (int i=0 ; i<sym.size() ; i++) {
                if (sym.at(i)==cur_sym) {
                    let=true; break;
                }
            }
            if (let==0) {
                sym.push_back(cur_sym);
            }
        } else {
            if(cur_sym == '*') {
                NFA star_sym = operands.top();
                operands.pop();
                operands.push(kleene(star_sym));
            } else if(cur_sym == '.') {
                operators.push(cur_sym);
            } else if(cur_sym == '+') {
                operators.push(cur_sym);
            } else if(cur_sym == '(') {
                operators.push(cur_sym);
            } else {
                op_count = 0;
                char c;
                op_sym = operators.top();
                if(op_sym == '(') continue;
                do {
                    operators.pop();
                    op_count++;
                } while(operators.top() != '(');
                operators.pop();
                NFA op1;
                NFA op2;
                vector<NFA> selections;
                if(op_sym == '.') {
                    for(int i = 0; i < op_count; i++) {
                        op2 = operands.top();
                        operands.pop();
                        op1 = operands.top();
                        operands.pop();
                        operands.push(concat(op1, op2));
                    }
                } else if(op_sym == '+'){
                    selections.assign(op_count + 1, NFA());
                    int tracker = op_count;
                    for(int i = 0; i < op_count + 1; i++) {
                        selections.at(tracker) = operands.top();
                        tracker--;
                        operands.pop();
                    }
                    operands.push(or_selection(selections, op_count+1));
                } else {

                }
            }
        }
    }

    NFA nfa=operands.top();
    nfa.symbol=sym;

    return nfa;
}


class DFA {
    public:

        vector<trans>        transitions;
        vector<vector<int> > entries;
        vector<bool>         marked;
        vector<int>          final_states;
        //vector<char>         symbol;

        /**
         * Add newly_created entry into DFA
         */
        int add_entry(vector<int> entry) {
            entries.push_back(entry);
            marked.push_back(false);
            return entries.size() - 1;
        }

        int get_entries_count() {
            return entries.size();
        }

        /**
         * Return the array position of the next unmarked entry
         */
        int next_unmarked_entry_idx() {
            for (int i = 0; i < marked.size(); i++) {
                if (!marked.at(i)) {
                    return i;
                }
            }

            return -1;
        }

        /**
         * mark the entry specified by index as marked (marked = true)
         */
        void mark_entry(int idx) {
            marked.at(idx) = true;
        }

        vector<int> entry_at(int i) {
            return entries.at(i);
        }

        int find_entry(vector<int> entry) {
            for (int i = 0; i < entries.size(); i++) {
                vector<int> it = entries.at(i);
                if (it == entry) {
                    return i;
                }
            }

            return -1;
        }

        void set_final_state(int nfa_fs) {
            if (nfa_fs) {
                for (int i = 0; i < entries.size(); i++) {
                    vector<int> entry = entries.at(i);

                    for (int j = 0; j < entry.size(); j++) {
                        int vertex = entry.at(j);
                        if (vertex == nfa_fs) {
                            final_states.push_back(i);
                        }
                    }
                }
            }
        }

        string get_final_state() {
            return join(final_states, ",");
        }

        void set_transition(int vertex_from, int vertex_to, char trans_symbol) {
            trans new_trans;
            new_trans.vertex_from = vertex_from;
            new_trans.vertex_to = vertex_to;
            new_trans.trans_symbol = trans_symbol;
            transitions.push_back(new_trans);
        }

        void display() {
            trans new_trans;
            cout<<"\n";
            for(int i = 0; i < transitions.size(); i++) {
                new_trans = transitions.at(i);
                cout<<"q"<<new_trans.vertex_from<<" {"<<join(entries.at(new_trans.vertex_from), ",")
                    <<"} -> q"<<new_trans.vertex_to<<" {"<<join(entries.at(new_trans.vertex_to), ",")
                    <<"} : Symbol - "<<new_trans.trans_symbol<<endl;
            }
            if (!final_states.empty()) {
                cout<<"\nThe final state is q : "<<join(final_states, ",")<<endl;
            } else {
                cout<<"\ndfa does not have a final state!"<<endl;
            }
        }

        void display_m() {
            trans new_trans;
            cout<<"\n";
            for(int i = 0; i < transitions.size(); i++) {
                new_trans = transitions.at(i);
                cout<<"q"<<new_trans.vertex_from << " -> q"<<new_trans.vertex_to << " : Symbol - "<<new_trans.trans_symbol<<endl;
            }
            if (!final_states.empty()) {
                cout<<"\nThe final state is q : "<<join(final_states, ",")<<endl;
            } else {
                cout<<"\ndfa does not have a final state!"<<endl;
            }
        }
};

/*DFA nfa_to_dfa(NFA nfa) {
    DFA dfa;

    const vector<int> start(1, 0);
    const vector<int> s0 = nfa.eclosure(start);
    vector<int> fs;

    int vertex_from = dfa.add_entry(s0);

    while (vertex_from != -1) {
        const vector<int> T = dfa.entry_at(vertex_from);
        dfa.mark_entry(vertex_from);

        const vector<char> symbols = nfa.find_possible_input_symbols(T);
        for (int i = 0; i < symbols.size(); i++) {
            char a = symbols.at(i);

            //TODO: add a eclosure cache : { state => eclosure }
            vector<int> U = nfa.eclosure(nfa.move(T, a));

            int vertex_to = dfa.find_entry(U);
            /*if (vertex_to == -1) { // U not already in S'
                if (nfa.final_state==-1) {
                    for (int j=0 ; j<U.size() ; j++) {
                        int u=U.at(j);
                        fs.push_back(u);
                    }
                }
                for (int j=0 ; j<U.size() ; j++) {
                    int u=U.at(j);
                    cout << "u " << u << endl;
                }
                vertex_to = dfa.add_entry(U);
            }

            dfa.set_transition(vertex_from, vertex_to, a);
            //cout << "t " << U << endl;
        }

        vertex_from = dfa.next_unmarked_entry_idx();
    }

    // The finish states of the DFA are those which contain any
    // of the finish states of the NFA.
    if (nfa.final_state==-1) {
        dfa.final_states=fs;
    }else {
        dfa.set_final_state(nfa.get_final_state());
    }

    return dfa;
}*/

DFA nfa_to_dfa(NFA nfa) {
    DFA dfa;

    const vector<int> start(1, 0);
    const vector<int> s0 = nfa.eclosure(start);

    int vertex_from = dfa.add_entry(s0);

    while (vertex_from != -1) {
        const vector<int> T = dfa.entry_at(vertex_from);
        dfa.mark_entry(vertex_from);

        const vector<char> symbols = nfa.find_possible_input_symbols(T);
        for (int i = 0; i < symbols.size(); i++) {
            char a = symbols.at(i);

            //TODO: add a eclosure cache : { state => eclosure }
            const vector<int> U = nfa.eclosure(nfa.move(T, a));

            int vertex_to = dfa.find_entry(U);
            if (vertex_to == -1) { // U not already in S'
                vertex_to = dfa.add_entry(U);
            }

            dfa.set_transition(vertex_from, vertex_to, a);
        }

        vertex_from = dfa.next_unmarked_entry_idx();
    }

    // The finish states of the DFA are those which contain any
    // of the finish states of the NFA.
    dfa.set_final_state(nfa.get_final_state());

    return dfa;
}

NFA contrary (DFA a) {
    int i;
    NFA result;

    bool arr[a.get_entries_count()];
    for (i=0 ; i<a.get_entries_count() ; i++) {
        arr[i]=0;
    }

    int final;
    for (i=0 ; i<a.final_states.size() ; i++) {
        final=a.final_states.at(i);
        arr[final]=1;
    }

    result.set_vertex(a.get_entries_count()+1);
    trans new_trans;

    for(i = 0; i < a.transitions.size(); i++) {
        new_trans = a.transitions.at(i);
        result.set_transition(new_trans.vertex_from, new_trans.vertex_to, new_trans.trans_symbol);
    }

    for (i=0 ; i<a.get_entries_count() ; i++) {
        if (!arr[i]) {
            result.set_transition(i, a.get_entries_count() + 1, '^');
            //cout << "i " << i << endl;
        }
    }
    result.set_final_state(a.get_entries_count()+1);

    return result;
}

NFA Union(DFA a, DFA b) {
    NFA result;
    result.set_vertex(a.get_entries_count() + b.get_entries_count() +2);

    int i;
    trans new_trans;

    result.set_transition(0, 1, '^');
    result.set_transition(0, a.get_entries_count()+1, '^');
    for(i = 0; i < a.transitions.size(); i++) {
        new_trans = a.transitions.at(i);
        result.set_transition(new_trans.vertex_from+1, new_trans.vertex_to+1, new_trans.trans_symbol);
        //cout << "nn " << new_trans.vertex_from+1 << " " << new_trans.vertex_to+1 << endl;
    }

    int final;
    for (i=0 ; i<a.final_states.size() ; i++) {
        final = a.final_states.at(i);
        result.set_transition(final +1, a.get_entries_count() + b.get_entries_count()+1, '^');
    }

    //result.set_transition(a.get_final_state(), a.get_entries_count() + b.get_entries_count()+1, '^');

    for(i = 0; i < b.transitions.size(); i++) {
        new_trans = b.transitions.at(i);
        result.set_transition(new_trans.vertex_from + a.get_entries_count()+1, new_trans.vertex_to + a.get_entries_count()+1, new_trans.trans_symbol);
    }

    for (i=0 ; i<b.final_states.size() ; i++) {
        final = b.final_states.at(i);
        result.set_transition(final + a.get_entries_count() +1, a.get_entries_count() + b.get_entries_count()+1, '^');
    }

    //result.set_transition(b.get_final_state(), a.get_entries_count() + b.get_entries_count() +1, '^');


    result.set_final_state(a.get_entries_count() + b.get_entries_count() +1);

    return result;
}

bool is_true(DFA a) {
    if (a.get_entries_count()==a.final_states.size())
        return true;
    return false;
}

/*bool are_equal( DFA& dfa1,  DFA& dfa2) {
    // Check if the number of entries, transitions, and final states are equal
    if (dfa1.entries.size() != dfa2.entries.size() ||
        dfa1.transitions.size() != dfa2.transitions.size() ||
        dfa1.final_states.size() != dfa2.final_states.size()) {
        return false;
    }

    // Check if the entries, transitions, and final states are equal
    for (int i = 0; i < dfa1.entries.size(); i++) {
        if (dfa1.entry_at(i) != dfa2.entry_at(i)) {
            return false;
        }
    }
    for (int i = 0; i < dfa1.transitions.size(); i++) {
        if (dfa1.transitions.at(i).vertex_from != dfa2.transitions.at(i).vertex_from ||
            dfa1.transitions.at(i).vertex_to != dfa2.transitions.at(i).vertex_to ||
            dfa1.transitions.at(i).trans_symbol != dfa2.transitions.at(i).trans_symbol) {
            return false;
        }
    }
    for (int i = 0; i < dfa1.final_states.size(); i++) {
        if (dfa1.final_states.at(i) != dfa2.final_states.at(i)) {
            return false;
        }
    }

    // The two DFAs are equal
    return true;
}*/

DFA minimize(DFA& dfa) {
    // Initialize the partition to two sets: final states and non-final states
    vector<vector<int> > partition(2);
    for (int i = 0; i < dfa.entries.size(); i++) {
        if (find(dfa.final_states.begin(), dfa.final_states.end(), i) != dfa.final_states.end()) {
            partition[0].push_back(i);
        } else {
            partition[1].push_back(i);
        }
    }

    // Keep partitioning until it doesn't change anymore
    bool changed = true;
    while (changed) {
        changed = false;

        // Partition each block in the current partition
        vector<vector<int> > new_partition;
        for (int i = 0; i < partition.size(); i++) {
            vector<int> block = partition[i];

            // Partition the block based on the transitions
            map<vector<int>, vector<int> > block_partitions;
            for (int j = 0; j < block.size(); j++) {
                int entry = block[j];
                vector<int> transitions_to;
                for (int k = 0; k < dfa.transitions.size(); k++) {
                    if (dfa.transitions[k].vertex_from == entry) {
                        transitions_to.push_back(dfa.transitions[k].vertex_to);
                    }
                }
                block_partitions[transitions_to].push_back(entry);
            }

            // Add the sub-blocks to the new partition
            for (auto p : block_partitions) {
                new_partition.push_back(p.second);
            }

            // Check if the partition has changed
            if (block_partitions.size() > 1) {
                changed = true;
            }
        }

        // Update the partition
        partition = new_partition;
    }

    // Create a new DFA based on the minimized partition
    DFA new_dfa;
    for (int i = 0; i < partition.size(); i++) {
        vector<int> entry = partition[i];
        new_dfa.add_entry(entry);

        // Check if the entry contains a final state
        bool contains_final_state = false;
        for (int j = 0; j < entry.size(); j++) {
            if (find(dfa.final_states.begin(), dfa.final_states.end(), entry[j]) != dfa.final_states.end()) {
                contains_final_state = true;
                break;
            }
        }
        if (contains_final_state) {
            new_dfa.final_states.push_back(i);
        }
    }
    for (int i = 0; i < dfa.transitions.size(); i++) {
        trans t = dfa.transitions[i];
        int new_vertex_from = new_dfa.find_entry(dfa.entry_at(t.vertex_from));
        int new_vertex_to = new_dfa.find_entry(dfa.entry_at(t.vertex_to));
        new_dfa.set_transition(new_vertex_from, new_vertex_to, t.trans_symbol);
    }

    // Update the original DFA to be the minimized DFA
    dfa = new_dfa;
    return dfa;
}




int size_order(string reg) {
    int i, j, Size= reg.length();

    for (i=1 ; i<reg.length()-1 ; i++) {
        if (i<reg.length()-2 && (reg[i+1]>= 'a' && reg[i+1]<= 'z') || (reg[i+1]>= 'A' && reg[i+1]<= 'Z') || (reg[i+1]>= '0' && reg[i+1]<= '9')) {
            if ((reg[i]>= 'a' && reg[i]<= 'z') || (reg[i]>= 'A' && reg[i]<= 'Z') || (reg[i]>= '0' && reg[i]<= '9') || reg[i]== '*' || reg[i]== ')') {
                Size++;
            }
        }

    }

    return Size;
}

string order(string reg, int Size) {
    int i, j;
    char regex[Size];
    for (i=0 , j=0; i<reg.length() ; i++, j++) {

        regex[j]=reg[i];

        if (i<reg.length()-2 && (reg[i+1]>= 'a' && reg[i+1]<= 'z') || (reg[i+1]>= 'A' && reg[i+1]<= 'Z') || (reg[i+1]>= '0' && reg[i+1]<= '9')) {
            if ((reg[i]>= 'a' && reg[i]<= 'z') || (reg[i]>= 'A' && reg[i]<= 'Z') || (reg[i]>= '0' && reg[i]<= '9') || reg[i]== '*' || reg[i]== ')') {
                j++;
                regex[j]='.';
            }
        } else if (i<reg.length()-2 && reg[i+1]>= '(' && (reg[i]== '*' || reg[i]== ')')) {
            j++;
            regex[j]='.';
        }
    }

    return regex;
}





int main() {

    cout<<"\n*****\t*****\t*****\n";
    cout<<"\nFORMAT : \n"
        <<"> Explicitly mention concatenation with a '.' operator \n"
        <<"> Enclose every concatenation and or section by parantheses \n"
        <<"> Enclose the entire regular expression with parantheses \n\n";

    /*cout<<"For example : \nFor the regular expression (a.(b|c))  -- \n";
    NFA example_nfa = re_to_nfa("(a.(b|c))");
    example_nfa.display();
*/
    cout<<"\n\nEnter the regular expressions in the above mentioned format - \n\n";
    string reg1,reg2;
    set<char> symbols;

    	cout<<endl<<"enter the regex: ";
		cin>>reg1;
		reg1= "(" + reg1 + ")";

		cout<<endl<<"enter the regex: ";
		cin>>reg2;
		reg2= "(" + reg2 + ")";

    NFA nfa1;
    DFA dfa1;
    NFA nfa2;
    DFA dfa2;
    cout<<"-------------------------------------------------------------------------------------------------";
	cout<<endl<<"NFA1 :"<<endl;
    nfa1 = re_to_nfa(reg1);
    nfa1.display();
    cout<<"\n==> DFA1 : \n";
    dfa1 = nfa_to_dfa(nfa1);
    dfa1.display();
    //cout<<"\n==> minimize DFA1 : \n";
    //dfa1= minimize(dfa1);
    //dfa1.display_m();
	cout<<"-------------------------------------------------------------------------------------------------";
    cout<<endl<<"NFA2 :"<<endl;
    nfa2 = re_to_nfa(reg2);
    nfa2.display();
    cout<<"\n==> DFA2 : \n";
    dfa2 = nfa_to_dfa(nfa2);
    dfa2.display();
    //cout<<"\n==> minimize DFA2 : \n";
    //dfa2= minimize(dfa2);
    //dfa2.display_m();

    /*cout<<"-------------------------------------------------------------------------------------------------";
    cout<<endl<<"NFA3 :"<<endl;
    NFA nfa3=Union(dfa1, nfa_to_dfa(contrary(dfa2)));
    nfa3.display();
    cout<<endl<<"DFA3 :"<<endl;
    DFA dfa3=nfa_to_dfa(nfa3);
    dfa3.display();

    cout<<"-------------------------------------------------------------------------------------------------";
    cout<<endl<<"NFA3 :"<<endl;
    NFA nfa4=Union(nfa_to_dfa(contrary(dfa1)), dfa2);
    nfa4.display();
    cout<<endl<<"DFA3 :"<<endl;
    DFA dfa4=nfa_to_dfa(nfa4);
    dfa4.display();

    /*NFA nfa3=Union(dfa1, dfa2);
    nfa3.display();
    cout<<"\n==> DFA3 : \n";
    DFA dfa = nfa_to_dfa(nfa3);
    dfa.display_m();*/



	/*if (is_true(dfa3) && is_true(dfa4)) {
        cout << "\n\nThe two Regular expression are equal." << endl;
    } else {
        cout << "\n\nThe two Regular expressions are not equal." << endl;
    }
    return 0;*/
}

/*(b*.(a.b.b*)*.(a|^))
((b|(a.b))*.(a|^))
(b*|(((b|(a.b))*.a).b*))*/

/*
(a+b)*
(a*.b*)*
*/

/*
b*.(a.b.b*)*.(a+^)
(b+(a.b))*.(a+^)
b*+(((b+(a.b))*.a).b*)
*/
