import BealMatveevBealV25B0Search.ChunkGroups.Group160
import BealMatveevBealV25B0Search.ChunkGroups.Group161
import BealMatveevBealV25B0Search.ChunkGroups.Group162
import BealMatveevBealV25B0Search.ChunkGroups.Group163
import BealMatveevBealV25B0Search.ChunkGroups.Group164
import BealMatveevBealV25B0Search.ChunkGroups.Group165
import BealMatveevBealV25B0Search.ChunkGroups.Group166
import BealMatveevBealV25B0Search.ChunkGroups.Group167
import BealMatveevBealV25B0Search.ChunkGroups.Group168
import BealMatveevBealV25B0Search.ChunkGroups.Group169

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_16 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 16 + 10 * g + i))
      (500 * (100 * 16 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_160 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_161 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_162 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_163 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_164 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_165 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_166 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_167 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_168 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_169 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
