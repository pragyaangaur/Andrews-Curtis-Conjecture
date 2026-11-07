import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 230 of the cap-16 certificate: slots 235520 .. 236543 -/
theorem chk_230 : chunkCheck 16 T stdSt 235520 1024 = true := by decide +kernel

end Row16
