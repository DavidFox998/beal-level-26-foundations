import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0300
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0301
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0302
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0303
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0304
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0305
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0306
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0307
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0308
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0309

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_030 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 30 + i)) (500 * (10 * 30 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0300
  by_cases h1 : i = 1
  · subst i
    exact chunk_0301
  by_cases h2 : i = 2
  · subst i
    exact chunk_0302
  by_cases h3 : i = 3
  · subst i
    exact chunk_0303
  by_cases h4 : i = 4
  · subst i
    exact chunk_0304
  by_cases h5 : i = 5
  · subst i
    exact chunk_0305
  by_cases h6 : i = 6
  · subst i
    exact chunk_0306
  by_cases h7 : i = 7
  · subst i
    exact chunk_0307
  by_cases h8 : i = 8
  · subst i
    exact chunk_0308
  by_cases h9 : i = 9
  · subst i
    exact chunk_0309
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
