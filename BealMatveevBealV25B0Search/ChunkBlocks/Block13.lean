import BealMatveevBealV25B0Search.ChunkGroups.Group130
import BealMatveevBealV25B0Search.ChunkGroups.Group131
import BealMatveevBealV25B0Search.ChunkGroups.Group132
import BealMatveevBealV25B0Search.ChunkGroups.Group133
import BealMatveevBealV25B0Search.ChunkGroups.Group134
import BealMatveevBealV25B0Search.ChunkGroups.Group135
import BealMatveevBealV25B0Search.ChunkGroups.Group136
import BealMatveevBealV25B0Search.ChunkGroups.Group137
import BealMatveevBealV25B0Search.ChunkGroups.Group138
import BealMatveevBealV25B0Search.ChunkGroups.Group139

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_13 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 13 + 10 * g + i))
      (500 * (100 * 13 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_130 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_131 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_132 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_133 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_134 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_135 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_136 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_137 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_138 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_139 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
