import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0440
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0441
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0442
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0443
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0444
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0445
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0446
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0447
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0448
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0449

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_044 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 44 + i)) (500 * (10 * 44 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0440
  by_cases h1 : i = 1
  · subst i
    exact chunk_0441
  by_cases h2 : i = 2
  · subst i
    exact chunk_0442
  by_cases h3 : i = 3
  · subst i
    exact chunk_0443
  by_cases h4 : i = 4
  · subst i
    exact chunk_0444
  by_cases h5 : i = 5
  · subst i
    exact chunk_0445
  by_cases h6 : i = 6
  · subst i
    exact chunk_0446
  by_cases h7 : i = 7
  · subst i
    exact chunk_0447
  by_cases h8 : i = 8
  · subst i
    exact chunk_0448
  by_cases h9 : i = 9
  · subst i
    exact chunk_0449
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
