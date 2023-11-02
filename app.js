import { ready } from 'https://lsong.org/scripts/dom.js';
import { h, render, useState, useEffect } from 'https://lsong.org/scripts/react/index.js';

import "https://lsong.org/js/application.js";

const App = () => {
  const [] = useState();
  useEffect(() => {
    console.log('App is ready');
  }, []);
  return [
    h('h2', null, "App"),
    h('ul', null, [
      h('li', null, "Demo")
    ])
  ]
}

ready(() => {
  const app = document.getElementById('app');
  render(h(App), app);
});