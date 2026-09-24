import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0590
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0591
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0592
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0593
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0594
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0595
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0596
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0597
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0598
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0599

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_059 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 59 + i)) (500 * (10 * 59 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0590
  by_cases h1 : i = 1
  · subst i
    exact chunk_0591
  by_cases h2 : i = 2
  · subst i
    exact chunk_0592
  by_cases h3 : i = 3
  · subst i
    exact chunk_0593
  by_cases h4 : i = 4
  · subst i
    exact chunk_0594
  by_cases h5 : i = 5
  · subst i
    exact chunk_0595
  by_cases h6 : i = 6
  · subst i
    exact chunk_0596
  by_cases h7 : i = 7
  · subst i
    exact chunk_0597
  by_cases h8 : i = 8
  · subst i
    exact chunk_0598
  by_cases h9 : i = 9
  · subst i
    exact chunk_0599
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
