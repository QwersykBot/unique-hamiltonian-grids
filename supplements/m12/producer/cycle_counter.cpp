#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <ctime>
#include <iomanip>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

// Exact undirected edge-subset enumeration, capped after two witnesses.
// UNKNOWN is mandatory when either search budget is exhausted.
// The only counted objects are connected spanning degree-two edge sets.
constexpr int MAXV=256, MAXE=512;
struct Graph {
  int m=0,n=0,V=0,E=0;
  std::array<int,MAXV> orig{}, deg{};
  std::array<std::array<int,4>,MAXV> adj{};
  std::array<int,MAXE> u{},v{};
  std::vector<int> deleted;
  bool parity=true;
  Graph(int mm,int nn,const std::vector<int>& del):m(mm),n(nn),deleted(del) {
    if(m<1||n<1||m*n>MAXV) throw std::runtime_error("unsupported dimensions");
    std::array<int,MAXV> map; map.fill(-1);
    std::array<bool,MAXV> gone{};
    for(int d:del) {
      if(d<0||d>=m*n||gone[d]) throw std::runtime_error("invalid or repeated deletion");
      gone[d]=true;
    }
    int black=0;
    for(int i=0;i<m*n;i++) if(!gone[i]) {map[i]=V;orig[V++]=i;black+=((i/n+i%n)%2==0);}
    parity=2*black==V;
    for(int a=0;a<V;a++) {
      int p=orig[a],r=p/n,c=p%n;
      for(int q:{r+1<m?p+n:-1,c+1<n?p+1:-1}) if(q>=0&&map[q]>=0) {
        int b=map[q];
        if(E>=MAXE) throw std::runtime_error("too many edges");
        u[E]=a;v[E]=b;adj[a][deg[a]++]=E;adj[b][deg[b]++]=E;E++;
      }
    }
  }
};
struct State {
  std::array<int8_t,MAXE> e{}; // 0 undecided, 1 selected, -1 forbidden
  std::array<uint8_t,MAXV> chosen{},unknown{};
  std::array<uint16_t,MAXV> parent{},size{};
};
struct Counter {
  const Graph& g;
  uint64_t nodes=0,maxnodes=0,degree_prunes=0,subtour_prunes=0,cut_prunes=0;
  int count=0,limitms=0;
  bool unknown=false;
  std::array<std::vector<int>,2> solutions;
  std::chrono::steady_clock::time_point start;
  clock_t cpu_start;
  double seconds=0,cpu_seconds=0;
  explicit Counter(const Graph& gg,uint64_t cap,int ms):g(gg),maxnodes(cap),limitms(ms){}
  int find(const State& s,int a) const {while(s.parent[a]!=a)a=s.parent[a];return a;}
  int other(int e,int a) const {return g.u[e]^g.v[e]^a;}
  // Return -1 for contradiction, 0 ordinarily, +1 for an entire Hamiltonian cycle.
  int assign(State& s,int e,int val,std::vector<int>& q) {
    if(s.e[e]) return s.e[e]==val?0:-1;
    int a=g.u[e],b=g.v[e];
    s.e[e]=val;s.unknown[a]--;s.unknown[b]--;
    q.push_back(a);q.push_back(b);
    if(val==1) {
      if(++s.chosen[a]>2||++s.chosen[b]>2){degree_prunes++;return -1;}
      int ra=find(s,a),rb=find(s,b);
      if(ra==rb) {
        if(s.size[ra]==g.V)return 1;
        subtour_prunes++;return -1;
      }
      if(s.size[ra]<s.size[rb])std::swap(ra,rb);
      s.parent[rb]=ra;s.size[ra]+=s.size[rb];
    }
    return 0;
  }
  int propagate(State& s) {
    std::vector<int> q; q.reserve(2*g.E+g.V);
    for(int a=0;a<g.V;a++)q.push_back(a);
    for(size_t pos=0;pos<q.size();pos++) {
      int a=q[pos],sel=s.chosen[a],avail=s.unknown[a];
      if(sel>2||sel+avail<2){degree_prunes++;return -1;}
      int val=sel==2?-1:(sel+avail==2?1:0);
      if(val) for(int j=0;j<g.deg[a];j++) {
        int e=g.adj[a][j];
        if(!s.e[e]) {int k=assign(s,e,val,q);if(k)return k;}
      }
    }
    return 0;
  }
  // Every Hamiltonian graph is vertex-biconnected. Run a standard Tarjan
  // test on selected-or-undecided edges; pruning a cut vertex is necessary.
  bool allowed_biconnected(const State& s) const {
    std::array<int,MAXV> disc{},low{};
    int tick=0,seen=0;bool valid=true;
    auto dfs=[&](auto&& self,int a,int pe)->void {
      disc[a]=low[a]=++tick;seen++;int children=0;
      for(int j=0;j<g.deg[a];j++) {
        int e=g.adj[a][j];if(s.e[e]==-1||e==pe)continue;
        int b=other(e,a);
        if(!disc[b]) {children++;self(self,b,e);low[a]=std::min(low[a],low[b]);
          if(pe!=-1&&low[b]>=disc[a])valid=false;
        } else low[a]=std::min(low[a],disc[b]);
      }
      if(pe==-1&&children>1)valid=false;
    };
    dfs(dfs,0,-1);
    return valid&&seen==g.V;
  }
  void found(const State& s) {
    if(count>=2)return;
    std::vector<int> out;out.reserve(g.V+1);
    int a=0,prev=-1;
    do {
      out.push_back(g.orig[a]);int next=-1;
      for(int j=0;j<g.deg[a];j++){int e=g.adj[a][j];if(s.e[e]==1){int b=other(e,a);if(b!=prev){next=b;break;}}}
      if(next<0||out.size()>size_t(g.V))throw std::runtime_error("bad cycle witness");
      prev=a;a=next;
    }while(a!=0);
    if(out.size()!=size_t(g.V))throw std::runtime_error("nonspanning cycle witness");
    out.push_back(g.orig[0]);solutions[count++]=std::move(out);
  }
  void search(State s) {
    if(count>=2||unknown)return;
    nodes++;
    if((maxnodes&&nodes>maxnodes)||
       ((nodes&1023)==0&&limitms>0&&std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-start).count()>=limitms)) {
      unknown=true;return;
    }
    int p=propagate(s);if(p<0)return;if(p>0){found(s);return;}
    if(!allowed_biconnected(s)){cut_prunes++;return;}
    int best=-1,bestavail=9,bestsel=-1;
    for(int a=0;a<g.V;a++)if(s.unknown[a]) {
      int u=s.unknown[a],c=s.chosen[a];
      if(u<bestavail||(u==bestavail&&c>bestsel)){best=a;bestavail=u;bestsel=c;}
    }
    if(best<0)throw std::runtime_error("unrecognized terminal state");
    int e=-1;
    for(int j=0;j<g.deg[best];j++)if(!s.e[g.adj[best][j]]){e=g.adj[best][j];break;}
    State yes=s;std::vector<int> queue;int a=assign(yes,e,1,queue);
    if(a==1)found(yes);else if(a==0)search(yes);
    if(count>=2||unknown)return;
    a=assign(s,e,-1,queue);if(a==1)found(s);else if(a==0)search(s);
  }
  void run() {
    start=std::chrono::steady_clock::now();cpu_start=clock();
    if(g.V>=4&&g.parity) {
      State s;
      for(int a=0;a<g.V;a++){s.unknown[a]=g.deg[a];s.parent[a]=a;s.size[a]=1;}
      search(s);
    }
    seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    cpu_seconds=double(clock()-cpu_start)/CLOCKS_PER_SEC;
  }
  const char* status() const {return count>=2?"AT_LEAST_TWO":unknown?"UNKNOWN":count==1?"EXACT_ONE":"EXACT_ZERO";}
  void output(const std::string& id,bool witnesses)const {
    std::cout<<"{\"id\":\""<<id<<"\",\"m\":"<<g.m<<",\"n\":"<<g.n<<",\"deleted\":[";
    for(size_t i=0;i<g.deleted.size();i++){if(i)std::cout<<',';std::cout<<g.deleted[i];}
    std::cout<<"],\"status\":\""<<status()<<"\",\"count_lower_bound\":"<<count
      <<",\"nodes\":"<<nodes<<",\"wall_seconds\":"<<std::setprecision(9)<<seconds
      <<",\"cpu_seconds\":"<<cpu_seconds<<",\"degree_prunes\":"<<degree_prunes
      <<",\"subtour_prunes\":"<<subtour_prunes<<",\"cut_prunes\":"<<cut_prunes;
    if(witnesses||count==1){std::cout<<",\"cycles\":[";for(int j=0;j<count;j++){if(j)std::cout<<',';std::cout<<'[';for(size_t i=0;i<solutions[j].size();i++){if(i)std::cout<<',';std::cout<<solutions[j][i];}std::cout<<']';}std::cout<<']';}
    std::cout<<"}\n"<<std::flush;
  }
};

#ifndef CYCLE_COUNTER_LIBRARY
int main(){
  std::ios::sync_with_stdio(false);std::cin.tie(nullptr);
  std::string line;
  while(std::getline(std::cin,line))try {
    if(line.empty()||line[0]=='#')continue;
    std::istringstream in(line);std::string id;int m,n,ms,witnesses,d;uint64_t cap;
    if(!(in>>id>>m>>n>>cap>>ms>>witnesses>>d))throw std::runtime_error("bad input header");
    std::vector<int> del(d);for(int& a:del)if(!(in>>a))throw std::runtime_error("missing deletion");
    std::string extra;if(in>>extra)throw std::runtime_error("extra input");
    Graph g(m,n,del);Counter c(g,cap,ms);c.run();c.output(id,witnesses);
  }catch(const std::exception& e){std::cerr<<"ERROR "<<e.what()<<" input="<<line<<'\n';return 2;}
}
#endif
