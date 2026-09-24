import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0230
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0231
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0232
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0233
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0234
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0235
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0236
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0237
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0238
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0239

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_023 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 23 + i)) (500 * (10 * 23 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0230
  by_cases h1 : i = 1
  · subst i
    exact chunk_0231
  by_cases h2 : i = 2
  · subst i
    exact chunk_0232
  by_cases h3 : i = 3
  · subst i
    exact chunk_0233
  by_cases h4 : i = 4
  · subst i
    exact chunk_0234
  by_cases h5 : i = 5
  · subst i
    exact chunk_0235
  by_cases h6 : i = 6
  · subst i
    exact chunk_0236
  by_cases h7 : i = 7
  · subst i
    exact chunk_0237
  by_cases h8 : i = 8
  · subst i
    exact chunk_0238
  by_cases h9 : i = 9
  · subst i
    exact chunk_0239
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
