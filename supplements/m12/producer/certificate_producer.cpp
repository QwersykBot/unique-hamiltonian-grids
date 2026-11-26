#define CYCLE_COUNTER_LIBRARY
#include "cycle_counter.cpp"
#include <fstream>
#include <set>

// Frozen Counter, frozen D4 enumeration/retry order, new witness serialization.
// Certificate labels and edge indices always refer to the ORIGINAL canonical D.
struct Producer {
  static constexpr int N=12, VERTICES=144, EDGES=264;
  std::array<std::array<int,VERTICES>,8> perm{},inverse{};
  std::array<int,VERTICES> right{},down{};
  std::array<uint64_t,3> raw{},canonical{},owned{},zeros{},multiples{};
  std::array<uint64_t,9> attempts_hist{};
  uint64_t nodes=0,records=0;
  double counter_cpu=0;
  int shard=0,shards=1;
  std::chrono::steady_clock::time_point start=std::chrono::steady_clock::now();
  clock_t cpu_start=clock();
  Producer(int s=0,int total=1):shard(s),shards(total) {
    if(total<1||s<0||s>=total)throw std::runtime_error("bad shard");
    for(int f=0;f<2;f++)for(int k=0;k<4;k++)for(int p=0;p<VERTICES;p++) {
      int r=p/N,c=p%N;
      if(f)std::swap(r,c);
      for(int q=0;q<k;q++){int rr=c;c=N-1-r;r=rr;}
      int image=r*N+c;perm[4*f+k][p]=image;inverse[4*f+k][image]=p;
    }
    right.fill(-1);down.fill(-1);int edge=0;
    for(int p=0;p<VERTICES;p++) {
      if(p%N+1<N)right[p]=edge++;
      if(p/N+1<N)down[p]=edge++;
    }
    if(edge!=EDGES)throw std::runtime_error("bad full-grid edge count");
  }
  static void header() {
    std::cout<<"{\"format\":\"m12-hc-certificate-v1\",\"n\":12,\"edge_order\":\"row-major-right-then-down\"}\n";
  }
  std::array<int,4> transformed(const std::array<int,4>& a,int d,int k)const {
    std::array<int,4>b{-1,-1,-1,-1};
    for(int i=0;i<d;i++)b[i]=perm[k][a[i]];
    if(d==2){if(b[1]<b[0])std::swap(b[0],b[1]);}
    else if(d==4)std::sort(b.begin(),b.end());
    return b;
  }
  std::string encode(const std::vector<int>& cycle,int k,const std::vector<int>& deleted)const {
    if(cycle.size()!=VERTICES-deleted.size()+1||cycle.front()!=cycle.back())
      throw std::runtime_error("wrong solution length or closure");
    std::array<bool,VERTICES> removed{},seen{};
    for(int p:deleted)removed[p]=true;
    std::array<uint8_t,66> nibbles{};int edge_count=0;
    for(size_t j=0;j+1<cycle.size();j++) {
      int a=inverse[k][cycle[j]],b=inverse[k][cycle[j+1]];
      if(removed[a]||seen[a])throw std::runtime_error("mapped witness is not spanning and simple");
      seen[a]=true;
      if(a>b)std::swap(a,b);
      int edge=-1;
      if(b==a+1&&a/N==b/N)edge=right[a];
      else if(b==a+N)edge=down[a];
      if(edge<0||edge>=EDGES)throw std::runtime_error("mapped witness uses nongrid edge");
      int digit=65-edge/4,mask=1<<(edge%4);
      if(nibbles[digit]&mask)throw std::runtime_error("mapped witness repeats edge");
      nibbles[digit]|=mask;edge_count++;
    }
    if(edge_count!=int(VERTICES-deleted.size()))throw std::runtime_error("bad witness edge count");
    for(int p=0;p<VERTICES;p++)if(seen[p]==removed[p])throw std::runtime_error("mapped vertex set mismatch");
    std::string out;out.reserve(66);
    for(int digit:nibbles)out.push_back("0123456789abcdef"[digit]);
    return out;
  }
  static void write_deleted(const std::vector<int>& del) {
    std::cout<<'[';for(size_t i=0;i<del.size();i++){if(i)std::cout<<',';std::cout<<del[i];}std::cout<<']';
  }
  void emit_case(const std::array<int,4>& del,int d) {
    const std::vector<int> original(del.begin(),del.begin()+d);
    constexpr std::array<int,8> order{0,2,1,3,4,6,5,7};
    int used=0;
    for(int k:order) {
      used++;auto dd=transformed(del,d,k);
      Graph g(N,N,std::vector<int>(dd.begin(),dd.begin()+d));
      Counter c(g,4096,0);c.run();nodes+=c.nodes;counter_cpu+=c.cpu_seconds;
      if(c.count>=2) {
        std::string one=encode(c.solutions[0],k,original),two=encode(c.solutions[1],k,original);
        if(one==two)throw std::runtime_error("identical mapped edge-set witnesses");
        std::cout<<'[';write_deleted(original);std::cout<<",\""<<one<<"\",\""<<two<<"\"]\n";
        multiples[d/2]++;records++;attempts_hist[used]++;return;
      }
      if(!c.unknown) {
        if(c.count==1)throw std::runtime_error("UNEXPECTED EXACT_ONE; refusing incomplete certificate");
        std::cout<<'[';write_deleted(original);std::cout<<",0]\n";
        zeros[d/2]++;records++;attempts_hist[used]++;return;
      }
    }
    throw std::runtime_error("UNRESOLVED after all orientations; refusing incomplete certificate");
  }
  void visit(std::array<int,4> del,int d) {
    raw[d/2]++;
    if(d==2){if(del[1]<del[0])std::swap(del[0],del[1]);}
    else if(d==4)std::sort(del.begin(),del.end());
    for(int k=1;k<8;k++)if(transformed(del,d,k)<del)return;
    uint64_t ordinal=canonical[d/2]++;
    if(ordinal%shards!=uint64_t(shard))return;
    owned[d/2]++;emit_case(del,d);
    if(records%20000==0)std::cerr<<"shard="<<shard<<" records="<<records<<" wall="
      <<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<'\n';
  }
  void run(const std::string& summary_path) {
    header();std::vector<int>b,w;
    for(int p=0;p<VERTICES;p++)(((p/N+p%N)%2==0)?b:w).push_back(p);
    visit({-1,-1,-1,-1},0);
    for(int a:b)for(int c:w)visit({a,c,-1,-1},2);
    for(size_t i=0;i<b.size();i++)for(size_t j=i+1;j<b.size();j++)
      for(size_t k=0;k<w.size();k++)for(size_t l=k+1;l<w.size();l++)visit({b[i],b[j],w[k],w[l]},4);
    if(raw!=std::array<uint64_t,3>{1,5184,6533136}||canonical!=std::array<uint64_t,3>{1,666,818316})
      throw std::runtime_error("enumeration total mismatch");
    std::ofstream out(summary_path);
    if(!out)throw std::runtime_error("cannot write summary");
    out<<"{\"shard\":"<<shard<<",\"shards\":"<<shards<<",\"records\":"<<records<<",\"nodes\":"<<nodes
      <<",\"counter_cpu_seconds\":"<<std::setprecision(12)<<counter_cpu
      <<",\"process_cpu_seconds\":"<<double(clock()-cpu_start)/CLOCKS_PER_SEC
      <<",\"wall_seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    auto array=[&](const char* name,const auto& values){out<<",\""<<name<<"\":[";for(size_t i=0;i<values.size();i++){if(i)out<<',';out<<values[i];}out<<']';};
    array("raw_by_d0_d2_d4",raw);array("canonical_by_d0_d2_d4",canonical);array("owned_by_d0_d2_d4",owned);
    array("zero_by_d0_d2_d4",zeros);array("multiple_by_d0_d2_d4",multiples);array("attempt_hist",attempts_hist);out<<"}\n";
    std::cerr<<"DONE shard="<<shard<<" records="<<records<<'\n';
  }
  void sample() {
    header();std::string line;std::set<std::vector<int>> seen;
    while(std::getline(std::cin,line)) {
      if(line.empty())continue;
      std::istringstream input(line);int d;
      if(!(input>>d)||(d!=0&&d!=2&&d!=4))throw std::runtime_error("bad sample size");
      std::array<int,4> del{-1,-1,-1,-1};int black=0;
      for(int i=0;i<d;i++){if(!(input>>del[i])||del[i]<0||del[i]>=VERTICES||(i&&del[i]<=del[i-1]))throw std::runtime_error("bad sample deletion");black+=(del[i]/N+del[i]%N)%2==0;}
      std::string extra;if(input>>extra)throw std::runtime_error("extra sample input");
      if(black*2!=d)throw std::runtime_error("unbalanced sample");
      for(int k=1;k<8;k++)if(transformed(del,d,k)<del)throw std::runtime_error("noncanonical sample");
      if(!seen.insert(std::vector<int>(del.begin(),del.begin()+d)).second)throw std::runtime_error("repeated sample");
      emit_case(del,d);
    }
    std::cerr<<"SAMPLE_COMPLETE records="<<records<<'\n';
  }
};
int main(int argc,char** argv)try {
  std::ios::sync_with_stdio(false);std::cin.tie(nullptr);
  if(argc==2&&std::string(argv[1])=="sample"){Producer p;p.sample();}
  else if(argc==5&&std::string(argv[1])=="full"){
    Producer p(std::stoi(argv[2]),std::stoi(argv[3]));p.run(argv[4]);
  }else throw std::runtime_error("usage: certificate_producer sample | full shard shards summary.json");
}catch(const std::exception& e){std::cerr<<"ERROR "<<e.what()<<'\n';return 2;}
