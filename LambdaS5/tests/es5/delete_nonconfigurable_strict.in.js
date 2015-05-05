"use strict"; var x = {a:1}; Object.seal(x); try { delete x.a } catch (x) { x.name }
