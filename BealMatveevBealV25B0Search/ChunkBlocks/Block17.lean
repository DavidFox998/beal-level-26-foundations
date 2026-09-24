import BealMatveevBealV25B0Search.ChunkGroups.Group170
import BealMatveevBealV25B0Search.ChunkGroups.Group171
import BealMatveevBealV25B0Search.ChunkGroups.Group172
import BealMatveevBealV25B0Search.ChunkGroups.Group173
import BealMatveevBealV25B0Search.ChunkGroups.Group174
import BealMatveevBealV25B0Search.ChunkGroups.Group175
import BealMatveevBealV25B0Search.ChunkGroups.Group176
import BealMatveevBealV25B0Search.ChunkGroups.Group177
import BealMatveevBealV25B0Search.ChunkGroups.Group178
import BealMatveevBealV25B0Search.ChunkGroups.Group179

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_17 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 17 + 10 * g + i))
      (500 * (100 * 17 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_170 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_171 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_172 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_173 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_174 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_175 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_176 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_177 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_178 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_179 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
