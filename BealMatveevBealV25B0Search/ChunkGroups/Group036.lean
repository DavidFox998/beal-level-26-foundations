import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0360
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0361
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0362
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0363
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0364
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0365
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0366
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0367
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0368
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0369

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_036 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 36 + i)) (500 * (10 * 36 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0360
  by_cases h1 : i = 1
  · subst i
    exact chunk_0361
  by_cases h2 : i = 2
  · subst i
    exact chunk_0362
  by_cases h3 : i = 3
  · subst i
    exact chunk_0363
  by_cases h4 : i = 4
  · subst i
    exact chunk_0364
  by_cases h5 : i = 5
  · subst i
    exact chunk_0365
  by_cases h6 : i = 6
  · subst i
    exact chunk_0366
  by_cases h7 : i = 7
  · subst i
    exact chunk_0367
  by_cases h8 : i = 8
  · subst i
    exact chunk_0368
  by_cases h9 : i = 9
  · subst i
    exact chunk_0369
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
