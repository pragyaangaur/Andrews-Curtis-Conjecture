import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 376 of the cap-17 certificate: slots 192512 .. 193023 -/
theorem chk_376 : chunkCheck 17 T stdSt 192512 512 = true := by decide +kernel

end Row17
