import BealMatveevBealV25B0Search.ChunkGroups.Group110
import BealMatveevBealV25B0Search.ChunkGroups.Group111
import BealMatveevBealV25B0Search.ChunkGroups.Group112
import BealMatveevBealV25B0Search.ChunkGroups.Group113
import BealMatveevBealV25B0Search.ChunkGroups.Group114
import BealMatveevBealV25B0Search.ChunkGroups.Group115
import BealMatveevBealV25B0Search.ChunkGroups.Group116
import BealMatveevBealV25B0Search.ChunkGroups.Group117
import BealMatveevBealV25B0Search.ChunkGroups.Group118
import BealMatveevBealV25B0Search.ChunkGroups.Group119

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_11 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 11 + 10 * g + i))
      (500 * (100 * 11 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_110 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_111 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_112 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_113 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_114 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_115 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_116 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_117 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_118 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_119 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
