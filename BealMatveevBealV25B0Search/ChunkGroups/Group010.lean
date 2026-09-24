import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0100
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0101
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0102
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0103
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0104
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0105
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0106
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0107
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0108
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0109

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_010 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 10 + i)) (500 * (10 * 10 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0100
  by_cases h1 : i = 1
  · subst i
    exact chunk_0101
  by_cases h2 : i = 2
  · subst i
    exact chunk_0102
  by_cases h3 : i = 3
  · subst i
    exact chunk_0103
  by_cases h4 : i = 4
  · subst i
    exact chunk_0104
  by_cases h5 : i = 5
  · subst i
    exact chunk_0105
  by_cases h6 : i = 6
  · subst i
    exact chunk_0106
  by_cases h7 : i = 7
  · subst i
    exact chunk_0107
  by_cases h8 : i = 8
  · subst i
    exact chunk_0108
  by_cases h9 : i = 9
  · subst i
    exact chunk_0109
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
