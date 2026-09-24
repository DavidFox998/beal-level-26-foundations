import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0610
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0611
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0612
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0613
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0614
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0615
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0616
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0617
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0618
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0619

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_061 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 61 + i)) (500 * (10 * 61 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0610
  by_cases h1 : i = 1
  · subst i
    exact chunk_0611
  by_cases h2 : i = 2
  · subst i
    exact chunk_0612
  by_cases h3 : i = 3
  · subst i
    exact chunk_0613
  by_cases h4 : i = 4
  · subst i
    exact chunk_0614
  by_cases h5 : i = 5
  · subst i
    exact chunk_0615
  by_cases h6 : i = 6
  · subst i
    exact chunk_0616
  by_cases h7 : i = 7
  · subst i
    exact chunk_0617
  by_cases h8 : i = 8
  · subst i
    exact chunk_0618
  by_cases h9 : i = 9
  · subst i
    exact chunk_0619
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
