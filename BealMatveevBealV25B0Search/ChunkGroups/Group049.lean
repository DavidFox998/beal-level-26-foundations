import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0490
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0491
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0492
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0493
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0494
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0495
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0496
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0497
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0498
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0499

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_049 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 49 + i)) (500 * (10 * 49 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0490
  by_cases h1 : i = 1
  · subst i
    exact chunk_0491
  by_cases h2 : i = 2
  · subst i
    exact chunk_0492
  by_cases h3 : i = 3
  · subst i
    exact chunk_0493
  by_cases h4 : i = 4
  · subst i
    exact chunk_0494
  by_cases h5 : i = 5
  · subst i
    exact chunk_0495
  by_cases h6 : i = 6
  · subst i
    exact chunk_0496
  by_cases h7 : i = 7
  · subst i
    exact chunk_0497
  by_cases h8 : i = 8
  · subst i
    exact chunk_0498
  by_cases h9 : i = 9
  · subst i
    exact chunk_0499
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
