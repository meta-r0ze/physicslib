// Exhaust every phase-negation-invariant marker-independent gate program.
// Native gate formula: flip direction iff phase belongs to S; always flip
// the marker at the occupied site, then stream and advance the native phase.
// This is a computational census of the explicit kind-1/kind-4 subclass,
// not a kernel certificate and not the full phase-table rule space.
#include <algorithm>
#include <array>
#include <cstdlib>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <string>
#include <tuple>

using Key = std::tuple<int,int,int,int,int,int>;
int main(int argc, char** argv) {
  if (argc != 2) { std::cerr << "usage: phase_gate_census OUTPUT.csv\n"; return 2; }
  constexpr std::array<int,7> sizes{3,5,7,9,11,13,43};
  std::map<Key,std::uint64_t> groups;
  std::array<std::uint64_t,44> cardinalities{};
  for (std::uint32_t selector=0; selector<(1u<<22); ++selector) {
    std::uint64_t phases = selector & 1u;
    for(int j=1;j<=21;++j) if((selector>>j)&1u)
      phases |= (1ull<<j)|(1ull<<(43-j));
    const int gates=__builtin_popcountll(phases);
    ++cardinalities[gates];
    int pos=0, direction=0, lo=0, hi=0;
    std::array<int,43> sites{}, velocities{};
    for(int t=0;t<43;++t) {
      sites[t]=pos;
      direction ^= (phases>>t)&1ull;
      velocities[t]=direction ? -1 : 1;
      pos += direction ? -1 : 1;
      lo=std::min(lo,pos);hi=std::max(hi,pos);
    }
    const int drift=pos;
    for(int t=0;t<43;++t)if(velocities[t]!=velocities[42-t])return 6;
    if ((drift&1)==0 || direction!=(gates&1)) return 3;
    for(int n:sizes) {
      int period, turns, displacement, visited;
      auto mod=[n](int x){return (x%n+n)%n;};
      std::uint64_t base=0;
      for(int x:sites)base^=1ull<<mod(x);
      if(gates&1) {
        // The invariant phase word is palindromic. The reverse half-period
        // retraces it. Only the two endpoints can have odd marker parity.
        std::uint64_t parity=base;
        for(int x:sites)parity^=1ull<<mod(drift-x);
        if(parity != ((1ull<<0)^(1ull<<mod(drift))))return 7;
        period=(parity==0) ? 86 : 172;
        turns=(period/43)*gates;
        displacement=0;
        visited=std::min(n,hi-lo+1);
      } else {
        // Drift is odd/nonzero. Position returns after n/gcd(n,drift)
        // clock periods; this odd-length walk cannot restore every marker.
        int q=n/std::gcd(n,std::abs(drift));
        std::uint64_t parity=0;
        const std::uint64_t limit=(1ull<<n)-1;
        for(int j=0;j<q;++j){
          int shift=mod(j*drift);
          parity^=shift ? ((base<<shift)|(base>>(n-shift)))&limit : base;
        }
        if(parity==0 || (__builtin_popcountll(parity)%2)!=1)return 8;
        period=86*q;
        turns=(period/43)*gates;
        displacement=2*q*drift;
        visited=n;
      }
      ++groups[{n,gates,period,turns,displacement,visited}];
    }
  }
  std::uint64_t sum=0;for(auto c:cardinalities)sum+=c;
  if(sum!=(1u<<22))return 4;
  std::ofstream out(argv[1]);
  if(!out)return 5;
  out<<"n,gate_count,period,turns,per_delta,canonical_displacement,visited_core,marker_rate_robust,phase_offset_robust,programs\n";
  for(const auto& [key,count]:groups) {
    auto [n,g,p,r,d,v]=key;
    out<<n<<','<<g<<','<<p<<','<<r<<','<<g<<','<<d<<','<<v<<",true,true,"<<count<<'\n';
  }
  std::cerr<<sum<<" invariant gate programs; "<<groups.size()<<" family rows\n";
  std::cerr<<"Opposite initial direction negates displacement. Arbitrary initial markers add spectator support; they do not change this dynamics.\n";
}
