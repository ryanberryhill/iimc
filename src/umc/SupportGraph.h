#ifndef _SUPPORT_GRAPH_
#define _SUPPORT_GRAPH_

#include "UMC.h"
#include "InductiveTrace.h"

#include <vector>
#include <set>

namespace UMC {

  typedef std::set<CubeID> SupportSet;

  class SupportGraph {
    const InductiveTrace & inductive_trace;
    Logger & logger;
    typedef std::unordered_map<CubeID, SupportSet> SupportMap;
    SupportMap cube_in_edges;
    SupportMap cube_out_edges;
    std::set<CubeID> supported_cubes;
    std::set<CubeID> known_cubes;

    bool isBetter(const SupportSet & lhs, const SupportSet & rhs) const;
    unsigned countLits(const SupportSet & ss) const;

    //stats
    int total, total_cnt;
    std::vector<int> in_deg_dist;
    std::vector<int> out_deg_dist;
    int needed_inits;
    int unknown_supp;

    void findUnsupportedCubes(const Cube & init_cube, std::set<CubeID> & unsupported) const;

    void addEdge(CubeID from, CubeID to);
    void removeEdge(CubeID from, CubeID to);
    bool removeEdgeIfExists(CubeID from, CubeID to);

    public:
      SupportGraph(InductiveTrace & trace) : inductive_trace(trace), logger(UMC::null_log) { }
      SupportGraph(InductiveTrace & trace, UMC::Logger & logger) : inductive_trace(trace), logger(logger) { }

      // Delete a cube - i.e., anything that it supports must have its support
      // set deleted. We do not delete the cube in any other sense
      void deleteCube(const Cube & cube);
      void deleteCube(const CubeID id);

      void recordSupport(const std::set<Cube> & support_set, const Cube & supported);
      void recordSupport(const std::set<CubeID> & support_set, CubeID & supported);

      void deleteSupport(const Cube & supported);
      void deleteSupport(CubeID & supported);

      std::pair<SupportSet::const_iterator, SupportSet::const_iterator>
        getInEdges(const Cube & cube) const;
      std::pair<SupportSet::const_iterator, SupportSet::const_iterator>
        getInEdges(CubeID id) const;
      std::pair<SupportSet::const_iterator, SupportSet::const_iterator>
        getOutEdges(const Cube & cube) const;
      std::pair<SupportSet::const_iterator, SupportSet::const_iterator>
        getOutEdges(CubeID id) const;
      std::pair<std::set<CubeID>::const_iterator, std::set<CubeID>::const_iterator>
        getSupportedCubeIDs() const;
      std::pair<std::set<CubeID>::const_iterator, std::set<CubeID>::const_iterator>
        getKnownCubeIDs() const;
      std::set<Cube> getSupportSet(const Cube & cube) const;

      bool hasSupportSet(const Cube & cube) const;
      bool hasSupportSet(CubeID id) const;

      size_t getInDegree(const Cube & cube) const;
      size_t getInDegree(CubeID id) const;
      size_t getOutDegree(const Cube & cube) const;
      size_t getOutDegree(CubeID id) const;

      int getLevel(const Cube & cube) const;
      int getLevel(CubeID id) const;

      int getMinSupportLevel(const Cube & cube) const;
      int getMinSupportLevel(CubeID id) const;

      bool isBad(const Cube & cube) const;
      bool isBad(CubeID id) const;

      std::string getAnnotation(const Cube & cube) const;
      std::string getAnnotation(CubeID cube) const;
      bool hasAnnotation(const Cube & cube) const;
      bool hasAnnotation(CubeID cube) const;

      void writeInfDot(std::ostream & os, const Cube & property = Cube()) const;
      void writeInfDot(const std::string & file, const Cube & property = Cube()) const;
      void writeDot(std::ostream & os, const Cube & property = Cube()) const;
      void writeDot(const std::string & file, const Cube & property = Cube()) const;

      void computeStats(const Cube & property, bool inf_only=false);
      void printStats(bool inf_only=false);
  };

  class SupportGraphDotWriter {
    typedef std::unordered_map<std::string, std::string> ParamMap;
    const SupportGraph & graph;
    CubeID property_id;

    std::set<CubeID> proof_cubes;
    std::unordered_map<CubeID, unsigned> cube_to_outdegree;
    // Cubes at index i are from level i
    // It's a map because we can have -1 (we weren't given a level for the
    // cube, though maybe this should be classed as a bug) or INT_MAX
    // (level infinity)
    std::map< int, std::set<CubeID> > ranked_cubes;

    std::unordered_map<CubeID, unsigned> computeOutDegrees() const;
    std::map<int, std::set<CubeID> > computeRanks() const;

    std::string dotPreamble() const;
    std::string dotPostamble() const;
    std::string dotCubeIdentifier(CubeID cube) const;
    std::string dotCube(CubeID cube) const;
    std::string dotEdge(CubeID from, CubeID to) const;
    std::string dotParams(const ParamMap & params) const;

    public:
    SupportGraphDotWriter(const SupportGraph & graph, CubeID property_id) :
      graph(graph),
      property_id(property_id)
    {
      proof_cubes = findTransitiveSupport(property_id);
      cube_to_outdegree = computeOutDegrees();
      ranked_cubes = computeRanks();
    }

    void writeInfDot(std::ostream & os) const;
    void writeDot(std::ostream & os) const;
    std::unordered_map<CubeID, unsigned>& getOutDegrees();
    void findTransitiveSupport(std::set<CubeID> & support) const;
    std::set<CubeID> findTransitiveSupport(CubeID cube) const;
  };

}

#endif

