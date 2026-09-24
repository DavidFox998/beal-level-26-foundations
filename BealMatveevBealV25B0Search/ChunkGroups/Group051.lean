import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0510
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0511
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0512
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0513
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0514
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0515
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0516
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0517
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0518
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0519

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_051 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 51 + i)) (500 * (10 * 51 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0510
  by_cases h1 : i = 1
  · subst i
    exact chunk_0511
  by_cases h2 : i = 2
  · subst i
    exact chunk_0512
  by_cases h3 : i = 3
  · subst i
    exact chunk_0513
  by_cases h4 : i = 4
  · subst i
    exact chunk_0514
  by_cases h5 : i = 5
  · subst i
    exact chunk_0515
  by_cases h6 : i = 6
  · subst i
    exact chunk_0516
  by_cases h7 : i = 7
  · subst i
    exact chunk_0517
  by_cases h8 : i = 8
  · subst i
    exact chunk_0518
  by_cases h9 : i = 9
  · subst i
    exact chunk_0519
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
