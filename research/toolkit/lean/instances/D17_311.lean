import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 311 of the cap-17 certificate: slots 159232 .. 159743 -/
theorem chk_311 : chunkCheck 17 T stdSt 159232 512 = true := by decide +kernel

end Row17
