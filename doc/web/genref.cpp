#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#define foreach(e,c) for(typeof(c.begin())e=c.begin();e!=c.end();++e)

using namespace std;

struct property {
  string name;
  string idescr;
  string descr;
  bool empty() { return name.empty() && idescr.empty() && descr.empty(); }
};
struct option : public property{
  vector<property> props; // props[0] is dummy
  bool empty() { return property::empty() && props.empty(); }
};
vector<option> opts; // opts[0] is dummy

option last_opt;
property last_prop;

vector<string> tpl_toks;


void add_prop() {
  if (last_prop.empty()) return;
  last_opt.props.push_back(last_prop);
  last_prop = property();
}

void add_opt() {
  add_prop();
  if (last_opt.empty()) return;
  opts.push_back(last_opt);
  last_opt = option();
}
string anchor(const string& s) { return string("option-") + s; }

string uglify(istringstream& iss) {
  string word, r;
  while (iss >> word) {
    r += " ";
    if (word[0] == '$') {
      r += "<code class=\"prettyprint\">";
      r += word.substr(1);
      r += "</code>";
    } else if (word[0] == '@') {
      r += "<a href=\"#";
      r += anchor(word.substr(1));
      r += "\">";
      r += word.substr(1);
      r += "</a>";
    } else {
      r += word;
    }
  }
  return r;
}

string uglify(const string& s) {
  istringstream iss(s);
  return string(s.find_first_not_of(' '), ' ') + uglify(iss) + "\n";
}

int advance(int t) {
  int cnt = 1;
  while (cnt) {
    ++t;
    if (t >= tpl_toks.size()) return t - 1;
    if (tpl_toks[t] == "\\foreach_option" || tpl_toks[t] == "\\foreach_property") ++cnt;
    if (tpl_toks[t] == "\\next") --cnt;
  }
  return t;
}

void process(int t, option opt, property prop) {
  int tt;
  while (t < tpl_toks.size()) {
    tt = t;
    if (tpl_toks[t] == "\\foreach_option") {
      foreach (o, opts) process(t+1, *o, prop);
      tt = advance(t + 1);
    } else if (tpl_toks[t] == "\\foreach_property") {
      foreach (p, opt.props) process(t+1, opt, *p);
      tt = advance(t + 1);
    } else if (tpl_toks[t] == "\\next") {
      return;
    } else if (tpl_toks[t] == "\\option_anchor") {
      cout << anchor(opt.name);
    } else if (tpl_toks[t] == "\\option") {
      cout << opt.name;
    } else if (tpl_toks[t] == "\\option_inline_descr") {
      cout << opt.idescr;
    } else if (tpl_toks[t] == "\\option_descr") {
      cout << opt.descr;
    } else if (tpl_toks[t] == "\\property") {
      cout << prop.name;
    } else if (tpl_toks[t] == "\\property_inline_descr") {
      cout << prop.idescr;
    } else if (tpl_toks[t] == "\\property_descr") {
      cout << prop.descr;
    } else {
      cout << tpl_toks[t];
    }
    t = tt + 1;
  }
}

bool isid(char c) { return isalpha(c) || c == '_'; }

int main(int argc, char* argv[]) {
  string line;
  int i = 0;
  if (argc != 3) return 1;
  ifstream descr_file(argv[1]);
  ifstream tpl_file(argv[2]);
  while (getline(descr_file, line)) {
    if (line.substr(0,4) == "    ") { // a line of description
      if (last_prop.name.empty()) { // for the option
        last_opt.descr += uglify(line.substr(4));
      } else { // for the property
        last_prop.descr += uglify(line.substr(4));
      }
    } else if (line.substr(0, 2) == "  ") { // a new property
      add_prop();
      istringstream iss(line);
      iss >> last_prop.name;
      last_prop.idescr = uglify(iss);
    } else { // a new option
      add_opt();
      istringstream iss(line);
      iss >> last_opt.name;
      last_opt.idescr = uglify(iss);
    }
  }
  add_opt();
  char c;
  string tok;
  while (tpl_file >> noskipws >> c) {
    if (c == '\\' || (!isid(c) && !tok.empty() && tok[0] == '\\')) {
      if (!tok.empty()) tpl_toks.push_back(tok);
      tok.clear();
    } 
    tok += c;
  }
  if (!tok.empty()) tpl_toks.push_back(tok);
  process(0, option(), property());
}
