import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 252 of the cap-17 certificate: slots 129024 .. 129535 -/
theorem chk_252 : chunkCheck 17 T stdSt 129024 512 = true := by decide +kernel

end Row17
