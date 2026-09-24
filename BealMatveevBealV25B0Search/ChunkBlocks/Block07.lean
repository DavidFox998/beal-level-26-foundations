import BealMatveevBealV25B0Search.ChunkGroups.Group070
import BealMatveevBealV25B0Search.ChunkGroups.Group071
import BealMatveevBealV25B0Search.ChunkGroups.Group072
import BealMatveevBealV25B0Search.ChunkGroups.Group073
import BealMatveevBealV25B0Search.ChunkGroups.Group074
import BealMatveevBealV25B0Search.ChunkGroups.Group075
import BealMatveevBealV25B0Search.ChunkGroups.Group076
import BealMatveevBealV25B0Search.ChunkGroups.Group077
import BealMatveevBealV25B0Search.ChunkGroups.Group078
import BealMatveevBealV25B0Search.ChunkGroups.Group079

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_07 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 7 + 10 * g + i))
      (500 * (100 * 7 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_070 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_071 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_072 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_073 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_074 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_075 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_076 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_077 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_078 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_079 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
