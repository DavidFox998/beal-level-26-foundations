import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1610
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1611
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1612
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1613
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1614
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1615
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1616
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1617
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1618
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1619

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_161 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 161 + i)) (500 * (10 * 161 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1610
  by_cases h1 : i = 1
  · subst i
    exact chunk_1611
  by_cases h2 : i = 2
  · subst i
    exact chunk_1612
  by_cases h3 : i = 3
  · subst i
    exact chunk_1613
  by_cases h4 : i = 4
  · subst i
    exact chunk_1614
  by_cases h5 : i = 5
  · subst i
    exact chunk_1615
  by_cases h6 : i = 6
  · subst i
    exact chunk_1616
  by_cases h7 : i = 7
  · subst i
    exact chunk_1617
  by_cases h8 : i = 8
  · subst i
    exact chunk_1618
  by_cases h9 : i = 9
  · subst i
    exact chunk_1619
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
