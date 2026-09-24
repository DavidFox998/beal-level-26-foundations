import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0710
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0711
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0712
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0713
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0714
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0715
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0716
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0717
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0718
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0719

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_071 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 71 + i)) (500 * (10 * 71 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0710
  by_cases h1 : i = 1
  · subst i
    exact chunk_0711
  by_cases h2 : i = 2
  · subst i
    exact chunk_0712
  by_cases h3 : i = 3
  · subst i
    exact chunk_0713
  by_cases h4 : i = 4
  · subst i
    exact chunk_0714
  by_cases h5 : i = 5
  · subst i
    exact chunk_0715
  by_cases h6 : i = 6
  · subst i
    exact chunk_0716
  by_cases h7 : i = 7
  · subst i
    exact chunk_0717
  by_cases h8 : i = 8
  · subst i
    exact chunk_0718
  by_cases h9 : i = 9
  · subst i
    exact chunk_0719
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
