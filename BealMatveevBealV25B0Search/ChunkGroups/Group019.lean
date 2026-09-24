import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0190
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0191
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0192
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0193
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0194
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0195
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0196
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0197
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0198
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0199

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_019 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 19 + i)) (500 * (10 * 19 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0190
  by_cases h1 : i = 1
  · subst i
    exact chunk_0191
  by_cases h2 : i = 2
  · subst i
    exact chunk_0192
  by_cases h3 : i = 3
  · subst i
    exact chunk_0193
  by_cases h4 : i = 4
  · subst i
    exact chunk_0194
  by_cases h5 : i = 5
  · subst i
    exact chunk_0195
  by_cases h6 : i = 6
  · subst i
    exact chunk_0196
  by_cases h7 : i = 7
  · subst i
    exact chunk_0197
  by_cases h8 : i = 8
  · subst i
    exact chunk_0198
  by_cases h9 : i = 9
  · subst i
    exact chunk_0199
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
