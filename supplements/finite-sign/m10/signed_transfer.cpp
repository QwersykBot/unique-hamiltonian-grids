#include <algorithm>
#include <array>
#include <gmpxx.h>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <queue>
#include <string>
#include <unordered_map>
#include <vector>
using cpp_int = mpz_class;
struct Choice {uint16_t z,out;};
struct Edge {int target; int sign;};
struct State {uint64_t code; std::vector<Edge> edges; int init=0,sinit=0,end=0,send=0;};
struct Transfer {
 int m; unsigned full; std::vector<std::vector<Choice>> choices; std::vector<char> ready;
 std::vector<State> states; std::unordered_map<uint64_t,int> ids;
 long long choices_checked=0,transitions=0;
 Transfer(int width):m(width),full((1u<<m)-1),choices(1u<<m),ready(1u<<m,0) {}
 unsigned active(uint64_t code) {unsigned a=0;for(int i=0;i<m;i++)if((code>>(4*i))&15)a|=1u<<i;return a;}
 const std::vector<Choice>& getchoices(unsigned act) {
  if(ready[act])return choices[act];ready[act]=1;
  auto& ans=choices[act];
  // Check all vertical masks once per active support, not once per pairing.
  for(unsigned z=0;z<=full;z++){
   unsigned prev=((z<<1)&full)|(z>>(m-1));
   // active rows forbid two vertical edges; inactive rows require at least one.
   if((act&z&prev)||((~act)&(~z)&(~prev)&full))continue;
   unsigned out=0;
   for(int i=0;i<m;i++)if(2-int((act>>i)&1)-int((z>>i)&1)-int((prev>>i)&1))out|=1u<<i;
   ans.push_back({(uint16_t)z,(uint16_t)out});
  }
  return ans;
 }
 int getid(uint64_t code){auto q=ids.find(code);if(q!=ids.end())return q->second;int k=states.size();ids.emplace(code,k);states.push_back({code,{}});return k;}
 bool glue(uint64_t code,Choice ch,uint64_t& next){
  ++choices_checked;std::array<int,16> parent;for(int i=0;i<m;i++)parent[i]=i;
  auto find=[&](int x){while(parent[x]!=x){parent[x]=parent[parent[x]];x=parent[x];}return x;};
  auto join=[&](int x,int y){x=find(x);y=find(y);if(x!=y)parent[y]=x;};
  for(int i=0;i<m;i++){int mate=int((code>>(4*i))&15)-1;if(mate>i)join(i,mate);if((ch.z>>i)&1)join(i,(i+1)%m);}
  std::array<int,16> first,second,count;first.fill(-1);second.fill(-1);count.fill(0);
  for(int i=0;i<m;i++)if((ch.out>>i)&1){int r=find(i);if(count[r]==0)first[r]=i;else if(count[r]==1)second[r]=i;count[r]++;}
  if(ch.out==0){int r=find(0);for(int i=1;i<m;i++)if(find(i)!=r)return false;next=0;return true;}
  next=0;
  for(int i=0;i<m;i++)if(find(i)==i){if(count[i]!=2)return false;int a=first[i],b=second[i];next|=uint64_t(b+1)<<(4*a);next|=uint64_t(a+1)<<(4*b);}
  return true;
 }
 void build(){
  for(Choice ch:getchoices(0)){uint64_t next;if(ch.out&&glue(0,ch,next)){int k=getid(next);states[k].init++;states[k].sinit+=((ch.z>>(m-1))&1)?-1:1;}}
  for(size_t idx=0;idx<states.size();idx++){
   uint64_t code=states[idx].code;std::vector<Edge> edges;int end=0,send=0;
   for(Choice ch:getchoices(active(code))){uint64_t next;if(!glue(code,ch,next))continue;int sign=((ch.z>>(m-1))&1)?-1:1;if(!ch.out){end++;send+=sign;}else{int target=getid(next);edges.push_back({target,sign});transitions++;}}
   states[idx].edges=std::move(edges);states[idx].end=end;states[idx].send=send;
  }
 }
 void write(int length,std::string path){
  std::ofstream out(path);out<<"{\"m\":"<<m<<",\"states\":"<<states.size()<<",\"edges\":"<<transitions<<",\"choices_checked\":"<<choices_checked<<",\"counts\":[";
  std::vector<cpp_int> vals(states.size()),sgn(states.size());for(size_t i=0;i<states.size();i++){vals[i]=states[i].init;sgn[i]=states[i].sinit;}
  for(int L=2;L<=length;L++){
   cpp_int sum=0,diff=0;for(size_t i=0;i<states.size();i++){sum+=vals[i]*states[i].end;diff+=sgn[i]*states[i].send;}
   if((sum+diff)%2!=0||sum<0||sum<diff||sum<-diff)throw std::runtime_error("invalid reconstructed count");
   cpp_int c=(sum+diff)/2,nc=(sum-diff)/2;
   if(L>2)out<<",";out<<"["<<L<<","<<c<<","<<nc<<","<<diff<<"]";
   if((L%2==0&&diff<=0)||(L%2==1&&diff>=0))std::cerr<<"SIGN FAILURE m="<<m<<" L="<<L<<" diff="<<diff<<"\n";
   if(L==length)break;
   std::vector<cpp_int> nv(states.size()),ns(states.size());for(size_t i=0;i<states.size();i++)for(auto e:states[i].edges){nv[e.target]+=vals[i];if(e.sign>0)ns[e.target]+=sgn[i];else ns[e.target]-=sgn[i];}vals.swap(nv);sgn.swap(ns);
  }
  out<<"]}\n";
 }
};
int main(int argc,char**argv){if(argc<4){std::cerr<<"Usage: signed_transfer WIDTH MAX_COLUMNS OUTPUT_JSON\n";return 2;}int m=std::stoi(argv[1]);if(m<3||m>14)return 3;auto start=std::chrono::steady_clock::now();Transfer t(m);t.build();auto built=std::chrono::steady_clock::now();std::cerr<<"m="<<m<<" states="<<t.states.size()<<" edges="<<t.transitions<<" build="<<std::chrono::duration<double>(built-start).count()<<"s\n";t.write(std::stoi(argv[2]),argv[3]);auto end=std::chrono::steady_clock::now();std::cerr<<"total="<<std::chrono::duration<double>(end-start).count()<<"s\n";}
