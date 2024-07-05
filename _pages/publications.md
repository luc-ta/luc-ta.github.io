---
layout: archive
title: "Publications"
sitemap: false
permalink: /publications/
author_profile: true
---

Note: remove the "sitemap" line in preamble when ready to publish

{% if site.author.googlescholar %}
  <div class="wordwrap">You can also find my articles on <a href="{{site.author.googlescholar}}">my Google Scholar profile</a>.</div>
{% endif %}

{% include base_path %}

{% for post in site.publications reversed %}
  {% include archive-single.html %}
{% endfor %}
