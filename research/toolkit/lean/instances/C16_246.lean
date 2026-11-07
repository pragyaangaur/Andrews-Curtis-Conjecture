import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 246 of the cap-16 certificate: slots 251904 .. 252927 -/
theorem chk_246 : chunkCheck 16 T stdSt 251904 1024 = true := by decide +kernel

end Row16
