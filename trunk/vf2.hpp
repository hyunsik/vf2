
#include <iostream>
#include <vector>
#include <utility>
#include <boost/graph/graph_traits.hpp>

namespace graph_alg
{
    typedef int EIndex;
    const EIndex NULL_INDEX = -1;

    namespace detail
    {
	class IndexIterator
	{
	    const std::vector<EIndex>* pcore;
	    const std::vector<int>*    pterm;
	    EIndex current;
	    
	    void find_next()
		{
		    while (current < static_cast<EIndex>(pcore->size()))
		    {
			if (pterm ?
			    (*pcore)[current] == NULL_INDEX && (*pterm)[current] :
			    (*pcore)[current] == NULL_INDEX)
			{
			    return;
			}
			++current;
		    }
		    current = NULL_INDEX;
		}
	public:
	    IndexIterator(const std::vector<EIndex>* pc = 0,
			  const std::vector<int>* pt = 0)
		: pcore(pc), pterm(pt), current(0)
		{
		    if (pc) 
			find_next();
		    else
			current = NULL_INDEX;
		}

	    EIndex get_v() const { return current; }
	    void next()          { ++current; find_next(); }
	};

	typedef std::pair<IndexIterator,IndexIterator> IndexIteratorPair;

	///////////////////////////////////////////////////////////////////////
	//		class MatchingPolicy
	// --------------------------------------------------------------------
	template<class G>
	class GGIsomorphismPolicy
	{
	public:
	    typedef typename boost::graph_traits<G>::vertex_descriptor V;
	    struct First { static bool test_eq(V v1, V v2) { return v1 == v2; } };
	    typedef First Second;
	    static bool check_term_count(int termout1, int termout2,
					 int termin1, int termin2,
					 int new1, int new2)
		{
		    return
			termout1 == termout2 &&
			termin1 == termin2 &&
			new1 == new2;
		}
	};


	template<class G>
	class GSGIsomorphismPolicy
	{
	};


	///////////////////////////////////////////////////////////////////////
	//		class DirectedPolicy
	// --------------------------------------------------------------------
	template<class G>
	class DirectedPolicy
	{
	public:
	    struct Len
	    {
		int t_len_out;
		int t_len_in;
		Len() :t_len_out(0), t_len_in(0) {}
	    };

	    class MappingArrays
	    {
		typedef typename boost::graph_traits<G>::vertex_descriptor VDescr;
		typedef typename boost::graph_traits<G>::edge_descriptor EDescr;

		std::vector<EIndex> core;
		std::vector<int> tou;
		std::vector<int> tin;
	    public:
		MappingArrays(int n)
		    : core(n, NULL_INDEX),
		      tou(n, 0),
		      tin(n, 0) {}

		static IndexIteratorPair pairs(const MappingArrays& ma1, const Len& len1,
					       const MappingArrays& ma2, const Len& len2);

		template<class MP_FN, class EDM>
		bool feasible(EDescr edge_g1, VDescr v_src_g1, VDescr v_trg_g1,
			      EDescr edge_g2, VDescr v_src_g2, VDescr v_trg_g2,
			      const G& g1, const G& g2,
			      const EDM& edm1, const EDM& edm2,
			      int* termout, int* termin, int* nnew) const;

		void add(const G& g, EIndex, EIndex, Len* len, int depth) {}
		void backtrack(const G& g, EIndex i, int depth) {}
	    };
	};

	template<class G>
	IndexIteratorPair DirectedPolicy<G>::MappingArrays::
	pairs(const MappingArrays& ma1, const Len& len1,
	      const MappingArrays& ma2, const Len& len2)
	{
	    if (len1.t_len_out > 0 && len2.t_len_out > 0)
		return IndexIteratorPair(IndexIterator(&ma1.core, &ma1.tou),
					 IndexIterator(&ma2.core, &ma2.tou));

	    if (len1.t_len_out + len2.t_len_out == 0 &&
		len1.t_len_in > 0 && len2.t_len_in > 0)
		return IndexIteratorPair(IndexIterator(&ma1.core, &ma1.tin),
					 IndexIterator(&ma2.core, &ma2.tin));

	    if (len1.t_len_out + len2.t_len_out + len1.t_len_in + len2.t_len_in == 0)
		return IndexIteratorPair(IndexIterator(&ma1.core),
					 IndexIterator(&ma2.core));
	    
	    return IndexIteratorPair();
	}
	

	template<class G>
	template<class MP_FN, class EDM>
	bool DirectedPolicy<G>::MappingArrays::
	feasible(EDescr edge_g1, VDescr v_src_g1, VDescr v_trg_g1,
		 EDescr edge_g2, VDescr v_src_g2, VDescr v_trg_g2,
		 const G& g1, const G& g2,
		 const EDM& edm1, const EDM& edm2,
		 int* termout, int* termin, int* nnew) const
	{
	    // =======================================================
	    // check OUT edges incidenced to edge_g1
	    // =======================================================
	    typename boost::graph_traits<G>::out_edge_iterator o_i, e_end;
	    
	    // -------------------------
	    // FROM v_src_g1
	    for (boost::tie(o_i,e_end) = out_edges(v_src_g1, g1); o_i != e_end; ++o_i)
	    {
		EDescr outedge_g1 = *o_i;
		if (edge_g1 == outedge_g1)
		    continue;
		EIndex index_outedge_g1 = edm1.get_edge_index(outedge_g1);
		if (core[index_outedge_g1] != NULL_INDEX)
		{
		    EDescr outedge_g1_to_g2 = edm2.get_edge_descriptor(core[index_outedge_g1]);
		    if (! MP_FN::test_eq(v_src_g2, source(outedge_g1_to_g2, g2)))
			return false;
		}
		else
		{
		    if (tou[index_outedge_g1]) ++*termout;
		    if (tin[index_outedge_g1]) ++*termin;
		    if (!tou[index_outedge_g1] && !tin[index_outedge_g1]) ++*nnew;
		}
	    }

	    // -------------------------
	    // FROM edge_g1.v_target
	    for (boost::tie(o_i,e_end) = out_edges(v_trg_g1, g1); o_i != e_end; ++o_i)
	    {
		EDescr outedge_g1 = *o_i;
		if (edge_g1 == outedge_g1)
		    continue;
		EIndex index_outedge_g1 = edm1.get_edge_index(outedge_g1);
		if (core[index_outedge_g1] != NULL_INDEX)
		{
		    EDescr outedge_g1_to_g2 = edm2.get_edge_descriptor(core[index_outedge_g1]);
		    if (! MP_FN::test_eq(v_trg_g2, source(outedge_g1_to_g2, g2)))
			return false;
		}
		else
		{
		    if (tou[index_outedge_g1]) ++*termout;
		    if (tin[index_outedge_g1]) ++*termin;
		    if (!tou[index_outedge_g1] && !tin[index_outedge_g1]) ++*nnew;
		}		
	    }


	    // =======================================================
	    // check IN edges incidenced to edge_g1
	    // =======================================================
	    typename boost::graph_traits<G>::in_edge_iterator i_i, i_end;

	    // -------------------------
	    // TO edge_g1.v_source
	    for (boost::tie(i_i,i_end) = in_edges(v_src_g1, g1); i_i != i_end; ++i_i)
	    {
		EDescr inedge_g1 = *i_i;
		if (edge_g1 == inedge_g1)
		    continue;
		EIndex index_inedge_g1 = edm1.get_edge_index(inedge_g1);
		if (core[index_inedge_g1] != NULL_INDEX)
		{
		    EDescr inedge_g1_to_g2 = edm2.get_edge_descriptor(core[index_inedge_g1]);
		    if (! MP_FN::test_eq(v_src_g2, target(inedge_g1_to_g2, g2)))
			return false;		    
		}
		else
		{
		    if (tou[index_inedge_g1]) ++*termout;
		    if (tin[index_inedge_g1]) ++*termin;
		    if (!tou[index_inedge_g1] && !tin[index_inedge_g1]) ++*nnew;
		}
	    }


	    // -------------------------
	    // TO edge_g1.v_target
	    for (boost::tie(i_i,i_end) = in_edges(v_trg_g1, g1); i_i != i_end; ++i_i)
	    {
		EDescr inedge_g1 = *i_i;
		if (edge_g1 == inedge_g1)
		    continue;
		EIndex index_inedge_g1 = edm1.get_edge_index(inedge_g1);
		if (core[index_inedge_g1] != NULL_INDEX)
		{
		    EDescr inedge_g1_to_g2 = edm2.get_edge_descriptor(core[index_inedge_g1]);
		    if (! MP_FN::test_eq(v_trg_g2, target(inedge_g1_to_g2, g2)))
			return false;
		}
		else
		{
		    if (tou[index_inedge_g1]) ++*termout;
		    if (tin[index_inedge_g1]) ++*termin;
		    if (!tou[index_inedge_g1] && !tin[index_inedge_g1]) ++*nnew;
		}

	    }

	    return true;
	}

	///////////////////////////////////////////////////////////////////////
	//		class UnDirectedPolicy
	// --------------------------------------------------------------------
	template<class G>
	class UnDirectedPolicy
	{
	public:
	    struct Len
	    {
		int t_len;
		Len() :t_len(0) {}
	    };

	    struct MappingArrays
	    {
		typedef typename boost::graph_traits<G>::vertex_descriptor VDescr;
		typedef typename boost::graph_traits<G>::edge_descriptor EDescr;
		std::vector<EIndex> core;
		std::vector<int> t;
	    public:
		MappingArrays(int n)
		    : core(n, NULL_INDEX),
		      t(n, 0) {}

		static IndexIteratorPair pairs(const MappingArrays& ma1, const Len& len1,
					       const MappingArrays& ma2, const Len& len2);

		template<class MP_FN, class EDM>
		bool feasible(EDescr edge_g1, VDescr v_src_g1, VDescr v_trg_g1,
			      EDescr edge_g2, VDescr v_src_g2, VDescr v_trg_g2,
			      const G& g1, const G& g2,
			      const EDM& edm1, const EDM& edm2,
			      int* termout, int* termin, int* nnew) const;

		void add(const G& g, EIndex, EIndex, Len* len, int depth) {}
		void backtrack(const G& g, EIndex i, int depth) {}
	    };
	};


	template<class G>
	IndexIteratorPair UnDirectedPolicy<G>::MappingArrays::
	pairs(const MappingArrays& ma1, const Len& len1,
	      const MappingArrays& ma2, const Len& len2)
	{
	    if (len1.t_len > 0 && len2.t_len > 0)
		return IndexIteratorPair(IndexIterator(ma1.core, ma1.t),
					 IndexIterator(ma2.core, ma2.t));

	    if (len1.t_len == 0 && len2.t_len == 0)
		return IndexIteratorPair(IndexIterator(ma1.core),
					 IndexIterator(ma2.core));

	    return IndexIteratorPair();
	}

	
	template<class G>
	template<class MP_FN, class EDM>
	bool UnDirectedPolicy<G>::MappingArrays::
	feasible(EDescr edge_g1, VDescr v_src_g1, VDescr v_trg_g1,
		 EDescr edge_g2, VDescr v_src_g2, VDescr v_trg_g2,
		 const G& g1, const G& g2,
		 const EDM& edm1, const EDM& edm2,
		 int* termout, int* termin, int* nnew) const
	{
	    // =======================================================
	    // check edges incidenced to edge_g1
	    // =======================================================
	    typename boost::graph_traits<G>::out_edge_iterator o_i, e_end;
	    
	    // -------------------------
	    // FROM v_src_g1
	    for (boost::tie(o_i,e_end) = out_edges(v_src_g1, g1); o_i != e_end; ++o_i)
	    {
		EDescr outedge_g1 = *o_i;
		if (edge_g1 == outedge_g1)
		    continue;
		EIndex index_outedge_g1 = edm1.get_edge_index(outedge_g1);
		if (core[index_outedge_g1] != NULL_INDEX)
		{
		    EDescr outedge_g1_to_g2 = edm2.get_edge_descriptor(core[index_outedge_g1]);
		    if (! MP_FN::test_eq(v_src_g2, source(outedge_g1_to_g2, g2)))
			return false;
		}
		else
		{
		    if (t[index_outedge_g1]) ++*termout;
		}
	    }

	    // -------------------------
	    // FROM edge_g1.v_target
	    for (boost::tie(o_i,e_end) = out_edges(v_trg_g1, g1); o_i != e_end; ++o_i)
	    {
		EDescr outedge_g1 = *o_i;
		if (edge_g1 == outedge_g1)
		    continue;
		EIndex index_outedge_g1 = edm1.get_edge_index(outedge_g1);
		if (core[index_outedge_g1] != NULL_INDEX)
		{
		    EDescr outedge_g1_to_g2 = edm2.get_edge_descriptor(core[index_outedge_g1]);
		    if (! MP_FN::test_eq(v_trg_g2, source(outedge_g1_to_g2, g2)))
			return false;
		}
		else
		{
		    if (t[index_outedge_g1]) ++*termout;
		}		
	    }

	    return true;
	}

	template<class G, class DirTag>
	struct DirPolicy_ : public DirectedPolicy<G> {};

	template<class G>
	struct DirPolicy_<G,boost::undirected_tag> : public UnDirectedPolicy<G> {};

	template<class G>
	struct DirPolicy
	    : public DirPolicy_<G,typename boost::graph_traits<G>::directed_category> {};
	

	///////////////////////////////////////////////////////////////////////
	//		class Shared
	// --------------------------------------------------------------------
	//
	// template parameters:
	//  Graph
	//  EDM
	//    EDescr get_descriptor(EIndex) const;
	//    EIndex get_index(Descr) const;
	//
	template<class G, class D>
	class Shared
	{
	public:
	    typedef G Graph;
	    typedef D EDM;

	    typename DirPolicy<G>::MappingArrays ma;
	    const G& graph;
	    const EDM& edm;


	    Shared(const G& g, const EDM& edm)
		: ma(num_edges(g)), graph(g), edm(edm) {}
	    
	    void add_pair(EIndex i, EIndex j,
			  typename DirPolicy<G>::Len* len, int depth)
		{ ma.add(graph, i, j, len, depth); }
	};


	///////////////////////////////////////////////////////////////////////
	//		class State
	// --------------------------------------------------------------------
	// template parameters:
	//  SH - Shared class
	//  VC
	//    bool operator() (VDescr,VDescr) const;
	//  EC
	//    bool operator() (EDescr,EDescr) const;
	//	
	template<class SH, class VC, class EC, class MP>
	class State
	{
	    typedef typename SH::Graph Graph;
	    typedef typename SH::EDM EDM;

	    int depth;

	    struct MPart
	    {
		SH* shared;
		typename DirPolicy<Graph>::Len len;
		EIndex last;
		
		MPart(SH* sh) :shared(sh) {}
		MPart(const MPart& r, EIndex i, EIndex j, int depth)
		    :shared(r.shared), len(r.len), last(i)
		    { shared->add_pair(i, j, &len, depth); }
		
	    } mp1, mp2;

	    const VC& vc;
	    const EC& ec;
	public:
	    State(SH* sh1, SH* sh2, const VC& vc, const EC& ec)
		: depth(0),
		  mp1(sh1),
		  mp2(sh2),
		  vc(vc), ec(ec)
		{}

	    State(const State& s, EIndex ei1, EIndex ei2)
		: depth(s.depth + 1),
		  mp1(s.mp1, ei1, ei2, depth),
		  mp2(s.mp2, ei2, ei1, depth),
		  vc(s.vc), ec(s.ec)
		{}

	    bool is_goal() const { return 0; }
	    bool is_dead() const { return 0; }
	    bool is_feasible(EIndex ei1, EIndex ei2) const;
	    void backtrack() {}
	    IndexIteratorPair pairs() const
		{
		    return
			DirPolicy<Graph>::MappingArrays::pairs(
			    mp1.shared->ma, mp1.len, mp2.shared->ma, mp2.len);
		}
	};


	template<class SH, class VC, class EC, class MP>
	bool State<SH,VC,EC,MP>::is_feasible(EIndex ei_g1, EIndex ei_g2) const
	{
	    typedef typename boost::graph_traits<Graph>::vertex_descriptor VDescr;
	    typedef typename boost::graph_traits<Graph>::edge_descriptor EDescr;

	    const Graph& g1 = mp1.shared->graph;
	    const Graph& g2 = mp2.shared->graph;
	    const EDM& edm1 = mp1.shared->edm;
	    const EDM& edm2 = mp2.shared->edm;
	    EDescr e_g1 = edm1.get_edge_descriptor(ei_g1);
	    EDescr e_g2 = edm2.get_edge_descriptor(ei_g2);

	    if (! ec(g1, g2, e_g1, e_g2))
		return false;
	    
	    VDescr v_src_g1 = source(e_g1, g1);
	    VDescr v_trg_g1 = target(e_g1, g1);
	    VDescr v_src_g2 = source(e_g2, g2);
	    VDescr v_trg_g2 = target(e_g2, g2);

	    if (!
		(vc(g1, g2, v_src_g1, v_src_g2) && vc(g1, g2, v_trg_g1, v_trg_g2))
		||
		(vc(g1, g2, v_src_g1, v_trg_g2) && vc(g1, g2, v_trg_g1, v_src_g2))
		)
		return false;

	    int termout1=0, termout2=0, termin1=0, termin2=0, new1=0, new2=0;	    

	    typedef typename MP::First First;
	    typedef typename MP::Second Second;
	    if (! mp1.shared->ma.template feasible<First>(e_g1, v_src_g1, v_trg_g1,
							  e_g2, v_src_g2, v_trg_g2,
							  g1, g2, edm1, edm2,
							  &termout1, &termin1, &new1))
		return false;

	    if (! mp1.shared->ma.template feasible<Second>(e_g2, v_src_g2, v_trg_g2,
							   e_g1, v_src_g1, v_trg_g1,
							   g2, g1, edm2, edm1,
							   &termout2, &termin2, &new2))
		return false;

	    return GGIsomorphismPolicy<Graph>::check_term_count(
		termout1, termout2, termin1, termin2, new1, new2);
	}


	///////////////////////////////////////////////////////////////////////
	//		function match_all
	// --------------------------------------------------------------------
	template<class S>
	void match_all(const S& s)
	{
	    if (s.is_goal())
	    {
		return;
	    }

	    if (s.is_dead())
	    {
		return;
	    }
	    
	    
	    IndexIteratorPair ip = s.pairs();
	    if (ip.second.get_v() == NULL_INDEX)
		return;
	    while (ip.first.get_v() != NULL_INDEX)
	    {
		s.is_feasible(ip.first.get_v(), ip.second.get_v());
		S h(s, ip.first.get_v(), ip.second.get_v());
		match_all(h);
		h.backtrack();
	    }
	}


	///////////////////////////////////////////////////////////////////////
	//		Defaults
	// --------------------------------------------------------------------
	//
	class BadIndex {};

	template<class G>
	class EDMDedault {
	public:	    
	    typedef typename boost::graph_traits<G>::edge_descriptor EDescr;
	    EDMDedault(const G& g);
	    EDescr get_edge_descriptor(EIndex i) const { return i2d[i]; }
	    EIndex get_edge_index(EDescr v) const
		{
		    EIndex n = i2d.size();
		    for (EIndex i = 0; i < n; ++i) if (i2d[i] == v) return i;
		    throw BadIndex();
		    return NULL_INDEX;
		}

	private:
	    std::vector<EDescr> i2d;
	    
	};
	

	template<class G>	
	EDMDedault<G>::EDMDedault(const G& g)
	{
	    i2d.reserve(num_edges(g));
	    typename boost::graph_traits<G>::edge_iterator i, i_end;
	    for (boost::tie(i,i_end) = edges(g); i != i_end; ++i)
		i2d.push_back(*i);
	}


	template<class G>
	struct VertexDefaultCompatible {
	    typedef typename boost::graph_traits<G>::vertex_descriptor VDescr;
	    bool operator() (const G&, const G&, VDescr, VDescr) const { return true; }
	};

	template<class G>
	struct EdgeDefaultCompatible {
	    typedef typename boost::graph_traits<G>::edge_descriptor EDescr;
	    bool operator() (const G&, const G&, EDescr, EDescr) const { return true; }
	};
	
    } // end: namespace detail


    ///////////////////////////////////////////////////////////////////////
    //		function isomorphism_all
    // --------------------------------------------------------------------
    //
    template<class G, class EDM, class VC, class EC>
    void graph_isomorphism_all(const G& g1, const G& g2,
			       const EDM& edm1, const EDM& edm2,
			       const VC& vc,
			       const EC& ec)
    {
	typedef detail::GGIsomorphismPolicy<G> IsoPolicy;
	typedef detail::Shared<G,EDM> SH;
	SH sh1(g1, edm1);
	SH sh2(g2, edm2);

	detail::State<SH,VC,EC,IsoPolicy> state(&sh1, &sh2, vc, ec);
	detail::match_all(state);
    }


    template<class G>
    void graph_isomorphism_all(const G& g1, const G& g2)
    {
	graph_isomorphism_all(g1, g2,
			      detail::EDMDedault<G>(g1), detail::EDMDedault<G>(g2),
			      detail::VertexDefaultCompatible<G>(),
			      detail::EdgeDefaultCompatible<G>());
    }
}
