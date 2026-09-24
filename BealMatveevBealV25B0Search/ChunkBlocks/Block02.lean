import BealMatveevBealV25B0Search.ChunkGroups.Group020
import BealMatveevBealV25B0Search.ChunkGroups.Group021
import BealMatveevBealV25B0Search.ChunkGroups.Group022
import BealMatveevBealV25B0Search.ChunkGroups.Group023
import BealMatveevBealV25B0Search.ChunkGroups.Group024
import BealMatveevBealV25B0Search.ChunkGroups.Group025
import BealMatveevBealV25B0Search.ChunkGroups.Group026
import BealMatveevBealV25B0Search.ChunkGroups.Group027
import BealMatveevBealV25B0Search.ChunkGroups.Group028
import BealMatveevBealV25B0Search.ChunkGroups.Group029

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_02 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 2 + 10 * g + i))
      (500 * (100 * 2 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_020 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_021 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_022 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_023 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_024 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_025 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_026 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_027 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_028 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_029 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
