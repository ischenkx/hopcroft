#include <iostream>
#include <vector>
#include <unordered_map>
#include <map>
#include <unordered_set>
#include <optional>
#include <stack>
#include <queue>
#include <utility>
#include <fstream>

struct State {
    std::map<std::string, State *> transitions;
    size_t id;
    bool terminal = false;

    explicit State(size_t _id) : id(_id), transitions() {}

    void connect(const std::string &input, State *other) {
        this->transitions[input] = other;
    }

    State *go(const std::string &input) {
        const auto &iter = transitions.find(input);
        if (iter == transitions.end()) return nullptr;
        return iter->second;
    }
};

class DFA {
    State *current = nullptr;
    size_t initial = 0;
    size_t seq = 0;
    std::unordered_map<size_t, State *> states;
    std::unordered_set<size_t> terminals;

    State *get_mutable_state(size_t id) {
        auto iter = states.find(id);
        if (iter == states.end()) return nullptr;
        return iter->second;
    }

public:

    size_t get_initial() const {
        return initial;
    }

    const std::unordered_map<size_t, State *> &get_states() const {
        return states;
    }

    const std::unordered_set<size_t> &get_terminals() const {
        return terminals;
    }

    const State *get_state(size_t id) const {
        auto iter = states.find(id);
        if (iter == states.end()) return nullptr;
        return iter->second;
    }

    size_t count_states() const {
        return states.size();
    }

    void remove_terminal(size_t id) {
        State *state = get_mutable_state(id);
        if (state == nullptr) return;
        state->terminal = false;
        terminals.erase(id);
    }

    void make_terminal(size_t id) {
        State *state = get_mutable_state(id);
        if (state == nullptr) return;
        state->terminal = true;
        terminals.insert(id);
    }

    void reset() {
        State *initial_state = get_mutable_state(initial);
        if (initial_state == nullptr) return;
        current = initial_state;
    }

    size_t make_state(size_t id = -1) {
        if (id == -1) {
            while (true) {
                id = seq++;
                auto existing_state = get_state(id);
                if (existing_state == nullptr) break;
            }
        }
        auto existing_state = get_state(id);
        if (existing_state != nullptr) return -1;
        states[id] = new State(id);
        return id;
    }

    bool go(const std::string &input) {
        if (current == nullptr) return false;
        auto next = current->go(input);
        if (next == nullptr) return false;
        current = next;
        return true;
    }

    void connect(size_t a, size_t b, const std::string &inp) {
        auto a_state = get_mutable_state(a);
        auto b_state = get_mutable_state(b);

        if (a_state == nullptr || b_state == nullptr) return;
        a_state->connect(inp, b_state);
    }

    using InverseMap = std::unordered_map<std::size_t, std::unordered_map<std::string, std::unordered_set<size_t>>>;
    using StateSet = std::unordered_set<std::size_t>;
    using Alphabet = std::unordered_set<std::string>;

    InverseMap get_inverse_map() const {
        InverseMap res;
        for (const auto &[from_id, fro]: states) {
            if (res.find(from_id) == res.end()) res[from_id] = {};
            for (const auto &[c, to]: fro->transitions) {
                if (res.find(to->id) == res.end()) res[to->id] = {};
                auto &to_map = res[to->id];
                if (to_map.find(c) == to_map.end()) to_map[c] = {};
                to_map[c].insert(from_id);
            }
        }
        return res;
    }

    void delete_state(size_t id, std::optional<InverseMap> &inv) {
        auto state = get_state(id);
        if (state == nullptr) return;
        if (inv == std::nullopt) {
            inv = get_inverse_map();
        }

        states.erase(id);


        if (state->terminal) terminals.erase(id);
        if (inv->find(id) != inv->end()) {
            for (const auto &[input, s]: (*inv)[id]) {
                for (size_t src_id: s) {
                    auto src = get_mutable_state(src_id);
                    if (src != nullptr) src->transitions.erase(input);
                }
            }
        }

        delete state;
    }

    StateSet active_states() const {
        std::unordered_set<size_t> visited;
        StateSet result;
        auto inverse_map = get_inverse_map();
        for (auto term: this->terminals) {
            std::stack<std::pair<size_t, int>> stack;
            stack.push({term, 0});
            while (!stack.empty()) {
                auto [id, cmd] = stack.top();
                stack.pop();
                switch (cmd) {
                    case 0:
                        stack.push({id, 1});
                        if (visited.find(id) != visited.end()) continue;
                        visited.insert(id);
                        if (initial == id) result.insert(id);
                        for (const auto &[_, sources]: inverse_map[id]) {
                            for (const auto state_id: sources) {
                                stack.push({state_id, 0});
                            }
                        }
                        break;
                    case 1:
                        for (const auto &[_, sources]: inverse_map[id]) {
                            if (result.find(id) != result.end()) break;
                            for (const auto state_id: sources) {
                                if (result.find(state_id) != result.end()) {
                                    result.insert(id);
                                }
                            }
                        }
                        break;
                }
            }
        }
        return result;
    }

    StateSet inactive_states() const {
        const auto active = active_states();
        StateSet inactive;
        for (const auto &[id, _]: states) {
            if (active.find(id) == active.end()) {
                inactive.insert(id);
            }
        }
        return inactive;
    }

    void remove_inactive_states() {
        std::optional<InverseMap> inv = std::make_optional(get_inverse_map());
        for (const auto id: inactive_states()) {
            delete_state(id, inv);
        }
    }

    Alphabet alphabet() const {
        Alphabet alpha;
        for (const auto &[id, state]: states) {
            for (const auto &[input, _]: state->transitions) {
                alpha.insert(input);
            }
        }
        return alpha;
    }

private:
    static std::optional<std::pair<std::vector<State *>, std::vector<State *>>>
    _hopcroft_split(std::unordered_map<std::size_t, std::size_t> &state2class,
                    const std::vector<State *> &R,
                    size_t C_id,
                    const std::string &a) {
        std::vector<State *> r1, r2;
        for (const auto r: R) {
            if (r->transitions.find(a) == r->transitions.end()) {
                r2.emplace_back(r);
                continue;
            }
            if (state2class[r->transitions[a]->id] == C_id) {
                r1.emplace_back(r);
            } else {
                r2.emplace_back(r);
            }
        }

        if (r1.empty() || r2.empty()) {
            return std::nullopt;
        }
        std::pair<std::vector<State *>, std::vector<State *>> res(r1, r2);
        return res;
    }

public:


    DFA *hopcroft() {
        std::vector<std::vector<State *>> classes;
        std::vector<State *> _terminals, non_terminals;
        std::unordered_map<size_t, size_t> state2class;
        std::queue<size_t> queue;
        Alphabet alpha = alphabet();
        InverseMap inverse_map = get_inverse_map();
        _terminals.reserve(terminals.size());
        non_terminals.reserve(states.size() - terminals.size());
        for (const auto [_, state]: states) {
            if (state->terminal) {
                _terminals.emplace_back(state);
            } else {
                non_terminals.emplace_back(state);
            }
        }

        if (!_terminals.empty()) classes.emplace_back(_terminals);
        if (!non_terminals.empty()) classes.emplace_back(non_terminals);

        for (size_t class_id = 0; class_id < classes.size(); class_id++) {
            queue.push(class_id);
            for (const auto state: classes[class_id]) {
                state2class[state->id] = class_id;
            }
        }

        while (!queue.empty()) {
            size_t class_id = queue.front();
            queue.pop();
            for (const std::string &input: alpha) {
                const auto &c = classes[class_id];
                std::unordered_set<size_t> involved;
                for (const State *state: c) {
                    auto &state_inv = inverse_map[state->id];
                    if (state_inv.find(input) == state_inv.end()) continue;
                    for (size_t fro_id: state_inv[input]) {
                        involved.insert(state2class[fro_id]);
                    }
                }

                for (size_t r_id: involved) {
                    auto split_class = _hopcroft_split(state2class, classes[r_id], class_id, input);
                    if (split_class == std::nullopt) continue;
                    auto [r1, r2] = *split_class;

                    if (r1.size() > r2.size()) std::swap(r1, r2);
                    classes[r_id] = r2;
                    classes.emplace_back(r1);
                    size_t new_id = classes.size() - 1;
                    for (State *s: r1) state2class[s->id] = new_id;
                    queue.push(new_id);
                }
            }
        }

        auto mdfa = new DFA();
        for (size_t i = 0; i < classes.size(); i++) {
            mdfa->make_state(i + 1);
        }

        for (size_t i = 0; i < classes.size(); i++) {
            auto &c = classes[i];
            size_t class_id = i + 1;
            for (State *state: c) {
                if (state->terminal) mdfa->make_terminal(class_id);
                if (initial == state->id) mdfa->initial = class_id;
                for (const auto &[input, to]: state->transitions) {
                    size_t to_class_id = state2class[to->id] + 1;
                    mdfa->connect(class_id, to_class_id, input);
                }
            }
        }
        return mdfa;
    }

private:
    static bool _isomorphism_check_dfs(
            std::unordered_set<std::size_t> &visited,
            std::unordered_map<std::size_t, std::size_t> &assoc_table,
            const State *s1,
            const State *s2
    ) {
        if (visited.find(s1->id) != visited.end()) return true;
        visited.insert(s1->id);

        if (s1->terminal != s2->terminal) return false;
        assoc_table[s1->id] = s2->id;

        if (s1->transitions.size() != s2->transitions.size()) return false;

        for (const auto &[inp, t1]: s1->transitions) {
            if (s2->transitions.find(inp) == s2->transitions.end()) {
                return false;
            }

            const State *t2 = s2->transitions.at(inp);

            if (visited.find(t1->id) != visited.end()) {
                if (t2->id != assoc_table[t1->id]) {
                    return false;
                }
            } else {
                if (!_isomorphism_check_dfs(visited, assoc_table, t1, t2)) {
                    return false;
                }
            }
        }

        return true;
    }


public:
    bool is_isomorphic(const DFA &other) {
        if (count_states() != other.count_states()) return false;

        std::unordered_set<std::size_t> visited;
        std::unordered_map<std::size_t, std::size_t> assoc_table;

        bool res = _isomorphism_check_dfs(visited,
                                          assoc_table,
                                          get_state(initial),
                                          other.get_state(other.get_initial()));

        return res && assoc_table.size() == count_states();
    }

    void set_initial(size_t id) {
        if (get_state(id) == nullptr) return;
        initial = id;
    }

    ~DFA() {
        for (const auto &[_, state]: states) delete state;
    }
};

DFA *read_dfa(std::ifstream &input_file) {
    /*
     * Format:
     * <amount of states> <amount of transitions> <amount of terminal states>
     * <list of terminal states>
     * <from1> <to1> <input1>
     * ...
     * <fromN> <toN> <inputN>
     *
     * NOTE: the initial state is always 1
     * */
    size_t n, m, k;
    input_file >> n >> m >> k;
    auto dfa = new DFA();

    for (int i = 0; i < n; i++) dfa->make_state(i + 1);

    for (int i = 0; i < k; i++) {
        size_t id;
        input_file >> id;
        dfa->make_terminal(id);
    }

    for (int i = 0; i < m; i++) {
        size_t from_id, to_id;
        std::string input;
        input_file >> from_id >> to_id >> input;
        dfa->connect(from_id, to_id, input);
    }

    dfa->set_initial(1);

    return dfa;
}

void dump_dfa(std::ofstream &output_file, DFA &dfa) {
    /*
     * Format:
     * <amount of states> <amount of transitions> <amount of terminal states>
     * <list of terminal states>
     * <from1> <to1> <input1>
     * ...
     * <fromN> <toN> <inputN>
     *
     * NOTE: the initial state is always 1
     * */
    size_t transitions_count = 0;
    size_t mapping_seq = 2;
    // used for a proper state enumeration
    std::unordered_map<size_t, size_t> mapping;

    for (const auto &[id, state]: dfa.get_states()) {
        if (dfa.get_initial() == id) mapping[id] = 1;
        else mapping[id] = mapping_seq++;
        transitions_count += state->transitions.size();
    }

    output_file << dfa.count_states() << " " << transitions_count << " " << dfa.get_terminals().size() << '\n';

    for (const auto terminal_state_id: dfa.get_terminals()) {
        output_file << mapping[terminal_state_id] << " ";
    }

    output_file << '\n';

    for (const auto &[id, state]: dfa.get_states()) {
        for (const auto &[inp, to]: state->transitions) {
            output_file << mapping[id] << " " << mapping[to->id] << " " << inp << '\n';
        }
    }
}

int main() {
    std::ifstream input_file;
    std::ofstream output_file;
    input_file.open("fastminimization.in");
    output_file.open("fastminimization.out");
    if (input_file.fail() || output_file.fail()) {
        std::cerr << "failed to open files..." << std::endl;
        return -1;
    }
    DFA *dfa = read_dfa(input_file);
    dfa->remove_inactive_states();
    auto mdfa = dfa->hopcroft();

    dump_dfa(output_file, *mdfa);

    delete dfa;
    delete mdfa;

    input_file.close();
    output_file.close();
    return 0;
}