import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0520
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0521
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0522
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0523
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0524
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0525
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0526
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0527
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0528
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0529

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_052 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 52 + i)) (500 * (10 * 52 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0520
  by_cases h1 : i = 1
  · subst i
    exact chunk_0521
  by_cases h2 : i = 2
  · subst i
    exact chunk_0522
  by_cases h3 : i = 3
  · subst i
    exact chunk_0523
  by_cases h4 : i = 4
  · subst i
    exact chunk_0524
  by_cases h5 : i = 5
  · subst i
    exact chunk_0525
  by_cases h6 : i = 6
  · subst i
    exact chunk_0526
  by_cases h7 : i = 7
  · subst i
    exact chunk_0527
  by_cases h8 : i = 8
  · subst i
    exact chunk_0528
  by_cases h9 : i = 9
  · subst i
    exact chunk_0529
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
