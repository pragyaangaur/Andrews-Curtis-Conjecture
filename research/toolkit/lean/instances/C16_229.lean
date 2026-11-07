import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 229 of the cap-16 certificate: slots 234496 .. 235519 -/
theorem chk_229 : chunkCheck 16 T stdSt 234496 1024 = true := by decide +kernel

end Row16
