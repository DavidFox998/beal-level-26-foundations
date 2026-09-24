import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0420
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0421
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0422
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0423
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0424
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0425
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0426
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0427
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0428
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0429

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_042 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 42 + i)) (500 * (10 * 42 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0420
  by_cases h1 : i = 1
  · subst i
    exact chunk_0421
  by_cases h2 : i = 2
  · subst i
    exact chunk_0422
  by_cases h3 : i = 3
  · subst i
    exact chunk_0423
  by_cases h4 : i = 4
  · subst i
    exact chunk_0424
  by_cases h5 : i = 5
  · subst i
    exact chunk_0425
  by_cases h6 : i = 6
  · subst i
    exact chunk_0426
  by_cases h7 : i = 7
  · subst i
    exact chunk_0427
  by_cases h8 : i = 8
  · subst i
    exact chunk_0428
  by_cases h9 : i = 9
  · subst i
    exact chunk_0429
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
